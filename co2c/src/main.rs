use ast_utils::AstRepr;
use clap::Parser;
use compile_commands::CompileCommand;
use itertools::Itertools;
use repr::{
    hir::{
        FuncSig, TyKind,
        resolver::{CompoundTypeData, Resolver, SymbolKind},
    },
    la_arena::Idx,
    mir::{Body, IntUnOp, LocalDecl, LocalKind, MirCtx, Operand, Place, RETURN_LOCAL, Rvalue},
};
use std::{collections::HashMap, fmt::Write};
use xshell::{Shell, cmd};

use crate::args::CcFlags;

mod args;
mod exp;

fn render_local(l: Idx<LocalDecl>, body: &Body) -> String {
    match &body.local_decls[l].kind {
        LocalKind::Real {
            storage: _,
            ident,
            is_arg: _,
        } => format!("l_{}_{}", l.into_raw().into_u32(), ident.name),
        LocalKind::Temp => format!("l_{}", l.into_raw().into_u32()),
    }
}

fn create_zeroed_object(ty: &TyKind) -> String {
    format!(
        "unsafe {{ ::std::mem::zeroed::<{}>() }}",
        convert_type_to_rust_type(ty)
    )
}

fn convert_sig_to_rust_sig(sig: &FuncSig) -> String {
    format!(
        "({}) -> {}",
        sig.params
            .iter()
            .enumerate()
            .map(|(i, p)| format!("arg{i}: {}", convert_type_to_rust_type(&p.ty.kind)))
            .chain(sig.variadic_param.then(|| "...".to_owned()))
            .join(", "),
        convert_type_to_rust_type(&sig.ret_ty.kind),
    )
}

fn convert_type_to_rust_type(ty: &TyKind) -> String {
    match &ty {
        TyKind::PrimTy(prim_ty_kind) => match prim_ty_kind {
            repr::hir::PrimTyKind::Bool => "i32",
            repr::hir::PrimTyKind::Char => "i8",
            repr::hir::PrimTyKind::Int => "i32",
            repr::hir::PrimTyKind::Float => "f32",
            repr::hir::PrimTyKind::Double => "f64",
            repr::hir::PrimTyKind::Void => "()",
        }
        .to_owned(),
        TyKind::Struct(id) => format!("Struct{}", id.into_raw().into_u32()),
        TyKind::Union(id) => format!("Union{}", id.into_raw().into_u32()),
        TyKind::Ptr { kind, quals: _ } => {
            if let TyKind::Func { sig } = &**kind {
                format!(
                    "RawFnPtr::<extern \"C\" fn{}>",
                    convert_sig_to_rust_sig(&sig)
                )
            } else {
                format!("*mut ({})", convert_type_to_rust_type(&kind))
            }
        }
        TyKind::Array { kind, size: _ } => {
            format!("[{}; 101]", convert_type_to_rust_type(kind))
        }
        TyKind::Func { sig: _ } => {
            panic!("Functions as a type do not have Rust equivalent.");
        }
    }
}

fn convert_place_to_rust_expr(p: &Place, body: &Body) -> String {
    let mut result = render_local(p.local, body);
    for proj in &p.projections {
        match proj {
            repr::mir::PlaceElem::Field(f) => {
                result = format!("({result}).{f}");
            }
            repr::mir::PlaceElem::Index(place) => {
                result = format!(
                    "({result}).offset(({}) as isize)",
                    convert_place_to_rust_expr(place, body)
                );
            }
            repr::mir::PlaceElem::Deref => {
                result = format!("*({result})");
            }
        }
    }
    result
}

fn convert_operand_to_rust_expr(o: &Operand, body: &Body) -> String {
    match o {
        Operand::Place(place) => convert_place_to_rust_expr(place, body),
        Operand::Const(c) => match c {
            repr::mir::Const::Lit(lit) => match &lit.kind {
                repr::hir::LitKind::Str(s) => {
                    format!(r#"(c"{s}".as_ptr() as *mut i8)"#)
                }
                repr::hir::LitKind::Char(c) => format!("{}", *c as u32),
                repr::hir::LitKind::Int(i) => i.to_string(),
                repr::hir::LitKind::Float(f) => f.to_string(),
            },
            repr::mir::Const::Symbol(idx) => convert_symbol_to_rust_symbol(*idx, body),
            repr::mir::Const::Sizeof(ty) => format!(
                "(::std::mem::size_of::<{}>() as i32)",
                convert_type_to_rust_type(&ty.kind),
            ),
        },
    }
}

fn convert_symbol_to_rust_symbol(idx: Idx<SymbolKind>, body: &Body<'_>) -> String {
    match &body.symbol_resolver.arena[idx] {
        SymbolKind::Var(var_decl) => {
            if var_decl.ty.kind.is_fn() {
                format!("{}", var_decl.ident.name)
            } else {
                format!("static_{}", var_decl.ident.name)
            }
        }
        SymbolKind::Func(func_decl) => func_decl.ident.name.clone(),
        SymbolKind::EnumVariant { value, span: _ } => value.to_string(),
        SymbolKind::Param(_) | SymbolKind::TyDef(_) => unreachable!(),
    }
}

fn convert_rvalue_to_rust_expr(
    rv: &Rvalue,
    body: &Body,
    type_tag_resolver: &Resolver<CompoundTypeData>,
) -> String {
    match rv {
        Rvalue::Use(o) => convert_operand_to_rust_expr(o, body),
        Rvalue::BinaryOp(bin_op, op1, op2) => {
            let op1 = convert_operand_to_rust_expr(op1, body);
            let op2 = convert_operand_to_rust_expr(op2, body);
            match bin_op {
                repr::mir::IntBinOp::Add => format!("({op1}) + ({op2})"),
                repr::mir::IntBinOp::Sub => format!("({op1}) - ({op2})"),
                repr::mir::IntBinOp::Mul => format!("({op1}) * ({op2})"),
                repr::mir::IntBinOp::Div => format!("({op1}) / ({op2})"),
                repr::mir::IntBinOp::Rem => format!("({op1}) % ({op2})"),
                repr::mir::IntBinOp::BitOr => format!("({op1}) | ({op2})"),
                repr::mir::IntBinOp::BitXor => format!("({op1}) ^ ({op2})"),
                repr::mir::IntBinOp::BitAnd => format!("({op1}) & ({op2})"),
                repr::mir::IntBinOp::Eq => format!("(({op1}) == ({op2})) as _"),
                repr::mir::IntBinOp::Lt => format!("(({op1}) < ({op2})) as _"),
                repr::mir::IntBinOp::Le => format!("(({op1}) <= ({op2})) as _"),
                repr::mir::IntBinOp::Ne => format!("(({op1}) != ({op2})) as _"),
                repr::mir::IntBinOp::Ge => format!("(({op1}) >= ({op2})) as _"),
                repr::mir::IntBinOp::Gt => format!("(({op1}) > ({op2})) as _"),
                repr::mir::IntBinOp::Shl => format!("({op1}) << ({op2})"),
                repr::mir::IntBinOp::Shr => format!("({op1}) >> ({op2})"),
            }
        }
        Rvalue::UnaryOp(un_op, operand) => {
            let operand = convert_operand_to_rust_expr(operand, body);
            match un_op {
                IntUnOp::Not => format!("if ({operand}) == 0 {{ 1 }} else {{ 0 }}"),
                IntUnOp::Neg => format!("-({operand})"),
                IntUnOp::Com => format!("!({operand})"),
                IntUnOp::Pos => format!("+({operand})"),
            }
        }
        Rvalue::AddrOf(place) => {
            let place = convert_place_to_rust_expr(place, body);
            format!("&raw mut ({place})")
        }
        Rvalue::AddrOfStatic(idx) => {
            let symbol = convert_symbol_to_rust_symbol(*idx, body);
            format!("&raw mut ({symbol})")
        }
        Rvalue::Call(func, args) => {
            let is_fn_ptr = body.type_of_operand(func).is_fn_ptr();
            let mut func = convert_operand_to_rust_expr(func, body);
            if is_fn_ptr {
                func = format!("({func}).materialize()");
            }
            format!(
                "({func}({}))",
                args.iter()
                    .map(|op| convert_operand_to_rust_expr(op, body))
                    .join(", ")
            )
        }
        Rvalue::Cast {
            value,
            from_type,
            to_type,
        } => {
            if to_type.is_fn_ptr() {
                if from_type.is_fn_ptr() {
                    format!(
                        "{}::from_raw(({}).data)",
                        convert_type_to_rust_type(to_type),
                        convert_operand_to_rust_expr(value, body),
                    )
                } else if from_type.is_fn() {
                    format!(
                        "{}::build({})",
                        convert_type_to_rust_type(to_type),
                        convert_operand_to_rust_expr(value, body),
                    )
                } else {
                    format!(
                        "{}::from_raw(({}) as *mut ())",
                        convert_type_to_rust_type(to_type),
                        convert_operand_to_rust_expr(value, body),
                    )
                }
            } else if from_type.is_fn_ptr() {
                format!(
                    "({}).data as ({})",
                    convert_operand_to_rust_expr(value, body),
                    convert_type_to_rust_type(to_type),
                )
            } else if from_type.is_array() && to_type.is_ptr() {
                format!(
                    "({}).as_mut_ptr()",
                    convert_operand_to_rust_expr(value, body),
                )
            } else {
                format!(
                    "({}) as ({})",
                    convert_operand_to_rust_expr(value, body),
                    convert_type_to_rust_type(to_type),
                )
            }
        }
        Rvalue::StructInitializing(idx, args) => match type_tag_resolver.get_data_by_res(idx) {
            CompoundTypeData::Struct { fields } => {
                format!(
                    "Struct{} {{ {} }}",
                    idx.into_raw().into_u32(),
                    fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| {
                            format!(
                                "{}: {}",
                                f.ident.name,
                                match args.get(i) {
                                    Some(op) => convert_operand_to_rust_expr(op, body),
                                    None => create_zeroed_object(&f.ty.kind),
                                }
                            )
                        })
                        .join(", "),
                )
            }
            CompoundTypeData::Union { fields: _ } => todo!(),
            CompoundTypeData::Enum | CompoundTypeData::DeclaredOnly => todo!(),
        },
        Rvalue::List(_) => format!("[505404i32; 101]"),
        Rvalue::PtrDiff(l, r) => {
            let l = convert_operand_to_rust_expr(l, body);
            let r = convert_operand_to_rust_expr(r, body);
            format!("({l}).offset_from({r}) as i32")
        }
        Rvalue::Empty => todo!(),
    }
}

fn lower_mir_body_to_rust_block(
    rust_src: &mut String,
    args_count: usize,
    mir: Body<'_>,
    type_tag_resolver: &Resolver<CompoundTypeData>,
) -> Result<(), anyhow::Error> {
    writeln!(rust_src, "{{ let mut bb = 0i32;")?;
    for (local, data) in mir
        .local_decls
        .iter()
        .take(1)
        .chain(mir.local_decls.iter().skip(args_count + 1))
    {
        let ty = &data.ty;
        writeln!(
            rust_src,
            "let mut {} = {};",
            render_local(local, &mir),
            create_zeroed_object(&ty.kind)
        )?;
    }
    writeln!(rust_src, "loop {{ unsafe {{ match bb {{")?;
    for (id, bb) in mir.basic_blocks.iter() {
        writeln!(rust_src, "{} => {{", id.into_raw().into_u32())?;
        for stmt in &bb.statements {
            match &stmt.kind {
                repr::mir::StatementKind::Assign(place, rvalue) => {
                    writeln!(
                        rust_src,
                        "{} = {};",
                        convert_place_to_rust_expr(place, &mir),
                        convert_rvalue_to_rust_expr(rvalue, &mir, type_tag_resolver)
                    )?;
                }
                repr::mir::StatementKind::Call(operand, operands) => {
                    writeln!(
                        rust_src,
                        "{}({});",
                        convert_operand_to_rust_expr(&operand, &mir),
                        operands
                            .iter()
                            .map(|o| convert_operand_to_rust_expr(o, &mir))
                            .join(", "),
                    )?;
                }
            }
        }
        match &bb.terminator.as_ref().map(|t| &t.kind) {
            Some(repr::mir::TerminatorKind::Goto { bb }) => {
                writeln!(rust_src, "bb = {};", bb.get_id())?;
                writeln!(rust_src, "continue;")?;
            }
            Some(repr::mir::TerminatorKind::SwitchInt { discr, targets }) => {
                let discr = convert_operand_to_rust_expr(discr, &mir);
                let [t1, t2] = targets;
                writeln!(rust_src, "if {discr} != 0 {{")?;
                writeln!(rust_src, "bb = {};", t1.get_id())?;
                writeln!(rust_src, "}} else {{")?;
                writeln!(rust_src, "bb = {};", t2.get_id())?;
                writeln!(rust_src, "}} continue;")?;
            }
            None | Some(repr::mir::TerminatorKind::Return) => {
                writeln!(rust_src, "break {};", render_local(RETURN_LOCAL, &mir))?;
            }
        }
        writeln!(rust_src, "}}")?;
    }
    writeln!(rust_src, "_ => unreachable!(), }} }} }} }}")?;
    Ok(())
}

fn main() -> anyhow::Result<()> {
    env_logger::init();

    let args = CcFlags::parse();
    dbg!(&args);

    let mut compile_db = vec![];

    for source_path in &args.sources {
        dbg!(source_path);
        let source = std::fs::read_to_string(source_path)?;
        eprintln!("{source}");
        compile_db.push(CompileCommand {
            directory: std::env::current_dir()?,
            file: compile_commands::SourceFile::File(source_path.into()),
            arguments: Some(compile_commands::CompileArgs::Arguments(vec![
                "cc".to_owned(),
                source_path.to_owned(),
            ])),
            command: None,
            output: None,
        });
    }

    let mut ast = AstRepr::construct(&compile_db)?;

    assert_eq!(ast.len(), 1);

    let ast = ast.pop().unwrap();

    dbg!(ast.source_info.code.len());
    eprintln!(
        "{}",
        String::from_utf8(ast.source_info.code.clone()).unwrap()
    );

    ast.create_dot_graph("../salam.dot")?;
    dbg!(&ast.tree);

    let hir_ctx = repr::hir::HirCtx::new(&ast);
    let (hir, global_resolver, type_tag_resolver) = hir_ctx.lower_to_hir();

    let mut rust_src = "#![no_main]\n#![allow(unused)]\n#![allow(non_snake_case)]\n#![allow(non_upper_case_globals)]".to_owned();

    writeln!(rust_src, r#"unsafe extern "C" {{"#)?;
    rust_src += r#"}

#[derive(Clone, Copy)]
#[repr(transparent)]
struct RawFnPtr<F: Copy> {
    data: *mut (),
    _p: ::std::marker::PhantomData<F>,
}

impl<F: Copy> RawFnPtr<F> {
    unsafe fn materialize(self) -> F {
        unsafe { *::std::mem::transmute::<_, &F>(&self.data) }
    }

    const fn build(f: F) -> Self {
        Self {
            data: unsafe { *::std::mem::transmute::<_, &*mut ()>(&f) },
            _p: ::std::marker::PhantomData,
        }
    }

    const fn from_raw(data: *mut ()) -> Self {
        Self {
            data,
            _p: ::std::marker::PhantomData,
        }
    }
}

fn assert<T: PartialEq + std::fmt::Debug>(x: T, y: T, msg: *const std::ffi::c_char) {
    unsafe {
        assert_eq!(x, y, "failed: {:?}", std::ffi::CStr::from_ptr(msg));
    }
}    
    "#;

    for (idx, data) in type_tag_resolver.arena.iter() {
        match data {
            CompoundTypeData::Struct { fields } => {
                writeln!(
                    rust_src,
                    "#[repr(C)] struct Struct{} {{",
                    idx.into_raw().into_u32()
                )?;
                for field in fields {
                    writeln!(
                        rust_src,
                        "{}: {},",
                        &field.ident.name,
                        convert_type_to_rust_type(&field.ty.kind)
                    )?;
                }
                writeln!(rust_src, "}}")?;
            }
            CompoundTypeData::Union { fields } => {
                writeln!(
                    rust_src,
                    "#[repr(C)] union Union{} {{",
                    idx.into_raw().into_u32()
                )?;
                for field in fields {
                    writeln!(
                        rust_src,
                        "{}: {},",
                        &field.ident.name,
                        convert_type_to_rust_type(&field.ty.kind)
                    )?;
                }
                writeln!(rust_src, "}}")?;
            }
            CompoundTypeData::Enum => (),
            CompoundTypeData::DeclaredOnly => {
                writeln!(
                    rust_src,
                    "#[repr(C)] struct Struct{} {{ _dummy: i8 }}",
                    idx.into_raw().into_u32()
                )?;
            }
        }
    }

    let mut function_declarations = HashMap::<String, Option<FuncSig>>::new();

    for item in hir {
        match item.kind {
            repr::hir::ItemKind::Func(func_def) => {
                let SymbolKind::Func(func_decl) = &func_def.symbol_resolver.arena[func_def.symbol]
                else {
                    unreachable!();
                };
                function_declarations.insert(func_decl.ident.name.clone(), None);
                let args_count = func_decl.sig.params.len();

                let mir_ctx = MirCtx::new(
                    &func_def.symbol_resolver,
                    &func_def.label_resolver,
                    &type_tag_resolver,
                    func_def.span,
                );
                let mir = mir_ctx.lower_to_mir(&func_def)?;

                eprintln!("{mir}");

                writeln!(
                    rust_src,
                    "#[unsafe(no_mangle)] extern \"C\" fn {}({}) -> {}",
                    func_decl.ident.name,
                    mir.local_decls
                        .iter()
                        .skip(1)
                        .take(args_count)
                        .map(|(local, data)| {
                            format!(
                                "mut {}: {}",
                                render_local(local, &mir),
                                convert_type_to_rust_type(&data.ty.kind),
                            )
                        })
                        .join(", "),
                    convert_type_to_rust_type(&func_decl.sig.ret_ty.kind),
                )?;

                eprintln!("{mir}");

                lower_mir_body_to_rust_block(&mut rust_src, args_count, mir, &type_tag_resolver)?;
            }
            repr::hir::ItemKind::Decl(items) => {
                for symbol in &items {
                    let decl = &global_resolver.arena[*symbol];
                    match decl {
                        SymbolKind::Var(var_decl) => {
                            if let TyKind::Func { sig } = &var_decl.ty.kind {
                                function_declarations
                                    .entry(var_decl.ident.name.clone())
                                    .or_insert(Some((**sig).clone()));
                            } else {
                                write!(
                                    rust_src,
                                    "static mut static_{}: {ty} = ",
                                    var_decl.ident.name,
                                    ty = convert_type_to_rust_type(&var_decl.ty.kind)
                                )?;
                                match &var_decl.init {
                                    Some(_) => {
                                        let label_resolver = Resolver::new();
                                        let mir_ctx = MirCtx::new(
                                            &global_resolver,
                                            &label_resolver,
                                            &type_tag_resolver,
                                            var_decl.span,
                                        );
                                        let mir = mir_ctx.lower_static_to_mir(&var_decl)?;

                                        lower_mir_body_to_rust_block(
                                            &mut rust_src,
                                            0,
                                            mir,
                                            &type_tag_resolver,
                                        )?;

                                        writeln!(rust_src, ";")?;
                                    }
                                    None => writeln!(
                                        rust_src,
                                        "{};",
                                        create_zeroed_object(&var_decl.ty.kind)
                                    )?,
                                }
                            }
                        }
                        SymbolKind::Func(_)
                        | SymbolKind::Param(_)
                        | SymbolKind::TyDef(_)
                        | SymbolKind::EnumVariant { .. } => unreachable!(),
                    }
                }
            }
            repr::hir::ItemKind::TyDef(_) => (),
            repr::hir::ItemKind::TaggedTypeSpecifier(_) | repr::hir::ItemKind::Empty => (),
        }
    }

    for (name, sig) in function_declarations
        .iter()
        .filter_map(|x| Some((x.0, x.1.as_ref()?)))
    {
        writeln!(
            rust_src,
            "unsafe extern \"C\" {{ fn {name}{}; }}",
            convert_sig_to_rust_sig(&sig),
        )?;
    }

    let out_file = args.output.unwrap_or_else(|| "a.out".to_owned());

    let sh = Shell::new()?;

    eprintln!("{rust_src}");

    let rust_file_path = "/tmp/co2_rust.rs";

    std::fs::write(rust_file_path, rust_src)?;
    // std::fs::copy(rust_file_path, "../co2c/src/exp.rs")?;

    let emit = if args.compile_only {
        &["--emit=obj"] as &[&str]
    } else {
        &[]
    };

    cmd!(
        sh,
        "rustc {emit...} -g --edition=2024 /tmp/co2_rust.rs -o {out_file}"
    )
    .run()?;

    Ok(())
}
