use anyhow::Context;
use ast_utils::AstRepr;
use clap::Parser;
use compile_commands::CompileCommand;
use itertools::Itertools;
use repr::{
    hir::{TyKind, resolver::SymbolKind},
    la_arena::Idx,
    mir::{Body, LocalDecl, LocalKind, MirCtx, Operand, Place, Rvalue},
};
use std::fmt::Write;
use tempfile::TempDir;
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

fn convert_type_to_rust_type(ty: &TyKind) -> String {
    match &ty {
        TyKind::PrimTy(prim_ty_kind) => match prim_ty_kind {
            repr::hir::PrimTyKind::Bool => "u8",
            repr::hir::PrimTyKind::Char => "u8",
            repr::hir::PrimTyKind::Int => "i32",
            repr::hir::PrimTyKind::Float => "f32",
            repr::hir::PrimTyKind::Double => "f64",
            repr::hir::PrimTyKind::Void => "()",
        }
        .to_owned(),
        TyKind::TyDef(idx) => todo!(),
        TyKind::Struct(ident) => todo!(),
        TyKind::Union(ident) => todo!(),
        TyKind::Enum(ident) => todo!(),
        TyKind::Ptr { kind, quals: _ } => format!("*mut ({})", convert_type_to_rust_type(&kind)),
        TyKind::Array { kind, size } => {
            format!("[{}; 101]", convert_type_to_rust_type(kind))
        }
        TyKind::Func { sig } => todo!(),
    }
}

fn convert_place_to_rust_expr(p: &Place, body: &Body) -> String {
    let mut result = render_local(p.local, body);
    for proj in &p.projections {
        match proj {
            repr::mir::PlaceElem::Field(_) => todo!(),
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
                    format!(r#"c"{s}".as_ptr()"#)
                }
                repr::hir::LitKind::Char(_) => todo!(),
                repr::hir::LitKind::Int(i) => i.to_string(),
                repr::hir::LitKind::Float(f) => f.to_string(),
            },
            repr::mir::Const::Symbol(idx) => match &body.symbol_resolver.arena[*idx] {
                SymbolKind::Var(var_decl) => var_decl.ident.name.clone(),
                SymbolKind::Func(func_decl) => func_decl.ident.name.clone(),
                SymbolKind::Param(param_decl) => todo!(),
                SymbolKind::TyDef(ty) => todo!(),
            },
            repr::mir::Const::Sizeof => format!("512404"),
        },
    }
}

fn convert_rvalue_to_rust_expr(rv: &Rvalue, body: &Body) -> String {
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
                repr::mir::IntBinOp::Eq => format!("(({op1}) == ({op2})) as i32"),
                repr::mir::IntBinOp::Lt => format!("(({op1}) < ({op2})) as i32"),
                repr::mir::IntBinOp::Le => format!("(({op1}) <= ({op2})) as i32"),
                repr::mir::IntBinOp::Ne => format!("(({op1}) != ({op2})) as i32"),
                repr::mir::IntBinOp::Ge => format!("(({op1}) >= ({op2})) as i32"),
                repr::mir::IntBinOp::Gt => format!("(({op1}) > ({op2})) as i32"),
                repr::mir::IntBinOp::Shl => format!("({op1}) << ({op2})"),
                repr::mir::IntBinOp::Shr => format!("({op1}) >> ({op2})"),
            }
        }
        Rvalue::UnaryOp(un_op, operand) => {
            let operand = convert_operand_to_rust_expr(operand, body);
            match un_op {
                repr::hir::UnOp::Not => format!("if ({operand}) == 0 {{ 1 }} else {{ 0 }}"),
                repr::hir::UnOp::Neg => format!("-({operand})"),
                repr::hir::UnOp::Com => format!("!({operand})"),
                repr::hir::UnOp::Pos => format!("+({operand})"),
                repr::hir::UnOp::AddrOf => format!("&raw mut ({operand})"),
                repr::hir::UnOp::Deref => format!("*({operand})"),
            }
        }
        Rvalue::Call(operand, operands) => todo!(),
        Rvalue::Cast {
            value,
            from_type,
            to_type,
        } => {
            if from_type.is_array() && to_type.is_ptr() {
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
        Rvalue::List(operands) => format!("[0i32; 101]"),
        Rvalue::PtrDiff(l, r) => {
            let l = convert_operand_to_rust_expr(l, body);
            let r = convert_operand_to_rust_expr(r, body);
            format!("({l}).offset_from({r}) as i32")
        }
        Rvalue::Empty => todo!(),
    }
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
    let hir = hir_ctx.lower_to_hir();

    let mut rust_src = "".to_owned();

    writeln!(rust_src, r#"unsafe extern "C" {{"#)?;
    writeln!(rust_src, r#"fn printf(...);"#)?;
    writeln!(rust_src, r#"fn scanf(...);"#)?;
    rust_src += r#"}
fn assert<T: PartialEq + std::fmt::Debug>(x: T, y: T, msg: *const std::ffi::c_char) {
    unsafe {
        assert_eq!(x, y, "failed: {:?}", std::ffi::CStr::from_ptr(msg));
    }
}    
    "#;

    for item in hir {
        match item.kind {
            repr::hir::ItemKind::Func(func_def) => {
                let SymbolKind::Func(func_decl) = &func_def.symbol_resolver.arena[func_def.symbol]
                else {
                    unreachable!();
                };
                writeln!(
                    rust_src,
                    "fn {}() {{ let mut bb = 0i32;",
                    func_decl.ident.name
                )?;
                let mir_ctx = MirCtx::new(
                    &func_def.symbol_resolver,
                    &func_def.label_resolver,
                    func_def.span,
                );
                let mir = mir_ctx.lower_to_mir(&func_def)?;

                eprintln!("{mir}");

                for (local, data) in mir.local_decls.iter() {
                    let ty = &data.ty;
                    writeln!(
                        rust_src,
                        "let mut {} = unsafe {{ ::std::mem::zeroed::<{}>() }};",
                        render_local(local, &mir),
                        convert_type_to_rust_type(&ty.kind)
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
                                    convert_rvalue_to_rust_expr(rvalue, &mir)
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
                    match &bb.terminator.as_ref().expect("Missing terminator").kind {
                        repr::mir::TerminatorKind::Goto { bb } => {
                            writeln!(rust_src, "bb = {};", bb.get_id())?;
                            writeln!(rust_src, "continue;")?;
                        }
                        repr::mir::TerminatorKind::SwitchInt { discr, targets } => {
                            let discr = convert_operand_to_rust_expr(discr, &mir);
                            let [t1, t2] = targets;
                            writeln!(rust_src, "if {discr} != 0 {{")?;
                            writeln!(rust_src, "bb = {};", t1.get_id())?;
                            writeln!(rust_src, "}} else {{")?;
                            writeln!(rust_src, "bb = {};", t2.get_id())?;
                            writeln!(rust_src, "}} continue;")?;
                        }
                        repr::mir::TerminatorKind::Return => {
                            writeln!(rust_src, "return;")?;
                        }
                    }
                    writeln!(rust_src, "}}")?;
                }
                writeln!(rust_src, "_ => unreachable!(), }} }} }} }}")?;
            }
            repr::hir::ItemKind::Decl(items) => {}
            repr::hir::ItemKind::TyDef(idx) => (),
        }
    }

    let out_file = args.output.unwrap_or_else(|| "a.out".to_owned());

    let sh = Shell::new()?;

    let temp_dir = TempDir::new()?;

    eprintln!("{rust_src}");

    let rust_file_path = temp_dir.path().join("rust.rs");
    std::fs::write(&rust_file_path, rust_src)?;
    std::fs::copy(&rust_file_path, "../co2c/src/exp.rs")
        .context("fail to copy temporary rust code")?;

    cmd!(sh, "rustc --edition=2024 {rust_file_path} -o {out_file}").run()?;

    Ok(())
}
