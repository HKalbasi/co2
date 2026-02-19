#![feature(rustc_private)]

use std::sync::OnceLock;

// use rustc_public_generative::{self as rustc_gen, DefinedCrateInfo, FileId};
use rustc_public_generative::{
    CrateGeneratorState, DependencyInfo, FileId, ForeignModItem, FunctionAbi, FunctionSignature,
    HirModule, HirModuleItem, HirStructure, HirStructureCtx, HirTy, generate,
    rustc_public::{
        DefId,
        mir::{
            BasicBlock as MirBasicBlock, Body, BorrowKind, ConstOperand, LocalDecl as MirLocalDecl,
            MutBorrowKind, Mutability, Operand as MirOperand, Place as MirPlace, Rvalue,
            Statement as MirStatement, StatementKind as MirStatementKind,
            Terminator as MirTerminator, TerminatorKind, UnwindAction,
        },
        ty::{
            AdtDef, FnDef, GenericArgKind, GenericArgs, IntTy, MirConst, Region, RegionKind,
            RigidTy, Span as PublicSpan, Ty, UintTy,
        },
    },
};

fn place(local: usize) -> MirPlace {
    MirPlace {
        local,
        projection: vec![],
    }
}

fn const_uint(value: u128, span: PublicSpan) -> MirOperand {
    let c = MirConst::try_from_uint(value, UintTy::Usize).expect("failed to build usize const");
    MirOperand::Constant(ConstOperand {
        span,
        user_ty: None,
        const_: c,
    })
}

fn fn_const_operand(
    fn_def: FnDef,
    generic_args: Vec<GenericArgKind>,
    span: PublicSpan,
) -> MirOperand {
    let fn_ty = Ty::from_rigid_kind(RigidTy::FnDef(fn_def, GenericArgs(generic_args)));
    let c = MirConst::try_new_zero_sized(fn_ty).expect("failed to build fn const");
    MirOperand::Constant(ConstOperand {
        span,
        user_ty: None,
        const_: c,
    })
}

fn dep_fn(deps: &DependencyInfo, path: &str) -> FnDef {
    if let Some(found) = deps
        .functions
        .iter()
        .find(|f| f.path == path && f.fn_def.is_some())
        .and_then(|f| f.fn_def)
    {
        return found;
    }

    if let Some(found) = deps
        .functions
        .iter()
        .find(|f| f.path.ends_with(path) && f.fn_def.is_some())
        .and_then(|f| f.fn_def)
    {
        return found;
    }

    if let Some(last) = path.rsplit("::").next() {
        let required_segments = path
            .split("::")
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>();
        if let Some(found) = deps
            .functions
            .iter()
            .find(|f| {
                f.path.ends_with(&format!("::{last}"))
                    && f.fn_def.is_some()
                    && !f.path.contains("::{closure")
                    && !f.path.contains("{{")
                    && required_segments.iter().all(|seg| f.path.contains(seg))
            })
            .and_then(|f| f.fn_def)
        {
            return found;
        }
    }

    let mut similar = deps
        .functions
        .iter()
        .filter(|f| {
            f.path.contains(path)
                || path.contains(&f.path)
                || path
                    .rsplit("::")
                    .next()
                    .is_some_and(|last| f.path.ends_with(&format!("::{last}")))
        })
        .map(|f| format!("{} (fn_def={})", f.path, f.fn_def.is_some()))
        .collect::<Vec<_>>();
    similar.sort();
    similar.truncate(20);
    panic!(
        "missing dependency function: {path}\nexample matches:\n{}",
        similar.join("\n")
    );
}

fn dep_adt(deps: &DependencyInfo, path: &str) -> AdtDef {
    if let Some(found) = deps.types.iter().find(|t| t.path == path).map(|t| t.adt) {
        return found;
    }

    if let Some(found) = deps
        .types
        .iter()
        .find(|t| t.path.ends_with(path))
        .map(|t| t.adt)
    {
        return found;
    }

    if let Some(last) = path.rsplit("::").next() {
        if let Some(found) = deps
            .types
            .iter()
            .find(|t| t.path.ends_with(&format!("::{last}")) && !t.path.contains("{{"))
            .map(|t| t.adt)
        {
            return found;
        }
    }

    let mut similar = deps
        .types
        .iter()
        .filter(|t| {
            t.path.contains(path)
                || path.contains(&t.path)
                || path
                    .rsplit("::")
                    .next()
                    .is_some_and(|last| t.path.ends_with(&format!("::{last}")))
        })
        .map(|t| t.path.clone())
        .collect::<Vec<_>>();
    similar.sort();
    similar.truncate(20);
    panic!(
        "missing dependency type: {path}\nexample matches:\n{}",
        similar.join("\n")
    );
}

struct State {
    file_id: FileId,

    main_fn: FnDef,
    write_fn: FnDef,
    open_fn: FnDef,
    read_fn: FnDef,
    close_fn: FnDef,
    malloc_fn: FnDef,
    free_fn: FnDef,
}

unsafe impl Send for State {}
unsafe impl Sync for State {}

impl CrateGeneratorState for State {
    fn hir_structure(ctx: HirStructureCtx) -> (Self, HirStructure) {
        let file_id = ctx.add_custom_file("/tmp/echo_file.rs", "fn main()");
        let span = ctx.span_in_file(file_id, 2, 5);

        let root_crate = ctx.root_crate_def_id();
        let foreign_mod =
            ctx.allocate_def_id(root_crate, rustc_public_generative::DefData::ForeignMod);
        let main_fn = FnDef(ctx.allocate_def_id(
            root_crate,
            rustc_public_generative::DefData::ValueNs("main".to_owned()),
        ));
        let write_fn = FnDef(ctx.allocate_def_id(
            foreign_mod,
            rustc_public_generative::DefData::ValueNs("write".to_owned()),
        ));
        let open_fn = FnDef(ctx.allocate_def_id(
            foreign_mod,
            rustc_public_generative::DefData::ValueNs("open".to_owned()),
        ));
        let read_fn = FnDef(ctx.allocate_def_id(
            foreign_mod,
            rustc_public_generative::DefData::ValueNs("read".to_owned()),
        ));
        let close_fn = FnDef(ctx.allocate_def_id(
            foreign_mod,
            rustc_public_generative::DefData::ValueNs("close".to_owned()),
        ));
        let malloc_fn = FnDef(ctx.allocate_def_id(
            foreign_mod,
            rustc_public_generative::DefData::ValueNs("malloc".to_owned()),
        ));
        let free_fn = FnDef(ctx.allocate_def_id(
            foreign_mod,
            rustc_public_generative::DefData::ValueNs("free".to_owned()),
        ));

        let usize_ty = || HirTy::usize_ty(span);
        let i8_ty = || HirTy::signed_ty(IntTy::I8, span);
        let ptr_i8_mut = || HirTy::new_ptr(i8_ty(), Mutability::Mut, span);

        let hir_structure = HirStructure {
            root: HirModule {
                span,
                items: vec![
                    HirModuleItem::Function {
                        name: "main".to_string(),
                        id: main_fn,
                        sig: FunctionSignature {
                            inputs: vec![],
                            output: HirTy::new_tuple(vec![], span),
                            abi: FunctionAbi::Rust,
                            is_unsafe: false,
                        },
                        span,
                    },
                    HirModuleItem::ForeignMod {
                        id: foreign_mod,
                        items: vec![
                            ForeignModItem::ForeignFunction {
                                name: "write".to_string(),
                                id: write_fn,
                                sig: FunctionSignature {
                                    inputs: vec![usize_ty(), ptr_i8_mut(), usize_ty()],
                                    output: usize_ty(),
                                    abi: FunctionAbi::C,
                                    is_unsafe: true,
                                },
                                span,
                            },
                            ForeignModItem::ForeignFunction {
                                name: "open".to_string(),
                                id: open_fn,
                                sig: FunctionSignature {
                                    inputs: vec![ptr_i8_mut(), usize_ty()],
                                    output: usize_ty(),
                                    abi: FunctionAbi::C,
                                    is_unsafe: true,
                                },
                                span,
                            },
                            ForeignModItem::ForeignFunction {
                                name: "read".to_string(),
                                id: read_fn,
                                sig: FunctionSignature {
                                    inputs: vec![usize_ty(), ptr_i8_mut(), usize_ty()],
                                    output: usize_ty(),
                                    abi: FunctionAbi::C,
                                    is_unsafe: true,
                                },
                                span,
                            },
                            ForeignModItem::ForeignFunction {
                                name: "close".to_string(),
                                id: close_fn,
                                sig: FunctionSignature {
                                    inputs: vec![usize_ty()],
                                    output: usize_ty(),
                                    abi: FunctionAbi::C,
                                    is_unsafe: true,
                                },
                                span,
                            },
                            ForeignModItem::ForeignFunction {
                                name: "malloc".to_string(),
                                id: malloc_fn,
                                sig: FunctionSignature {
                                    inputs: vec![usize_ty()],
                                    output: ptr_i8_mut(),
                                    abi: FunctionAbi::C,
                                    is_unsafe: true,
                                },
                                span,
                            },
                            ForeignModItem::ForeignFunction {
                                name: "free".to_string(),
                                id: free_fn,
                                sig: FunctionSignature {
                                    inputs: vec![ptr_i8_mut()],
                                    output: HirTy::new_tuple(vec![], span),
                                    abi: FunctionAbi::C,
                                    is_unsafe: true,
                                },
                                span,
                            },
                        ],
                    },
                ],
            },
        };
        (
            State {
                file_id,

                main_fn,
                write_fn,
                open_fn,
                read_fn,
                close_fn,
                malloc_fn,
                free_fn,
            },
            hir_structure,
        )
    }

    fn emit_mir(&mut self, ctx: HirStructureCtx, def: DefId) -> Body {
        assert_eq!(self.main_fn.0, def);

        let span: PublicSpan = ctx.span_in_file(self.file_id, 0, 2);

        let deps = ctx.dependencies();

        let write = self.write_fn;
        let open = self.open_fn;
        let read = self.read_fn;
        let close = self.close_fn;
        let malloc = self.malloc_fn;
        let free = self.free_fn;

        let std_env_args = dep_fn(&deps, "std::env::args");
        let iter_nth = dep_fn(&deps, "std::iter::Iterator::nth");
        let option_unwrap = dep_fn(&deps, "std::option::Option::unwrap");
        let result_unwrap = dep_fn(&deps, "std::result::Result::unwrap");
        let cstring_new = dep_fn(&deps, "std::ffi::CString::new");
        let cstring_into_raw = dep_fn(&deps, "std::ffi::CString::into_raw");

        let args_adt = dep_adt(&deps, "std::env::Args");
        let string_adt = dep_adt(&deps, "std::string::String");
        let cstring_adt = dep_adt(&deps, "std::ffi::CString");
        let nul_error_adt = dep_adt(&deps, "std::ffi::NulError");
        let option_adt = dep_adt(&deps, "std::option::Option");
        let result_adt = dep_adt(&deps, "std::result::Result");

        let args_ty = Ty::from_rigid_kind(RigidTy::Adt(args_adt, GenericArgs(vec![])));
        let string_ty = Ty::from_rigid_kind(RigidTy::Adt(string_adt, GenericArgs(vec![])));
        let cstring_ty = Ty::from_rigid_kind(RigidTy::Adt(cstring_adt, GenericArgs(vec![])));
        let nul_error_ty = Ty::from_rigid_kind(RigidTy::Adt(nul_error_adt, GenericArgs(vec![])));
        let option_string_ty = Ty::from_rigid_kind(RigidTy::Adt(
            option_adt,
            GenericArgs(vec![GenericArgKind::Type(string_ty)]),
        ));
        let result_cstring_ty = Ty::from_rigid_kind(RigidTy::Adt(
            result_adt,
            GenericArgs(vec![
                GenericArgKind::Type(cstring_ty),
                GenericArgKind::Type(nul_error_ty),
            ]),
        ));

        let args_ref_ty = Ty::new_ref(
            Region {
                kind: RegionKind::ReErased,
            },
            args_ty,
            Mutability::Mut,
        );
        let usize_ty = Ty::usize_ty();
        let i8_ty = Ty::signed_ty(IntTy::I8);
        let ptr_i8_mut = Ty::new_ptr(i8_ty, Mutability::Mut);

        let locals = vec![
            MirLocalDecl {
                ty: Ty::new_tuple(&[]),
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: args_ty,
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: args_ref_ty,
                span,
                mutability: Mutability::Not,
            },
            MirLocalDecl {
                ty: option_string_ty,
                span,
                mutability: Mutability::Not,
            },
            MirLocalDecl {
                ty: string_ty,
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: result_cstring_ty,
                span,
                mutability: Mutability::Not,
            },
            MirLocalDecl {
                ty: cstring_ty,
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: ptr_i8_mut,
                span,
                mutability: Mutability::Not,
            },
            MirLocalDecl {
                ty: usize_ty,
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: ptr_i8_mut,
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: usize_ty,
                span,
                mutability: Mutability::Mut,
            },
            MirLocalDecl {
                ty: usize_ty,
                span,
                mutability: Mutability::Mut,
            },
        ];

        let blocks = vec![
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(std_env_args, vec![], span),
                        args: vec![],
                        destination: place(1),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![MirStatement {
                    kind: MirStatementKind::Assign(
                        place(2),
                        Rvalue::Ref(
                            Region {
                                kind: RegionKind::ReErased,
                            },
                            BorrowKind::Mut {
                                kind: MutBorrowKind::Default,
                            },
                            place(1),
                        ),
                    ),
                    span,
                }],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(iter_nth, vec![GenericArgKind::Type(args_ty)], span),
                        args: vec![MirOperand::Move(place(2)), const_uint(1, span)],
                        destination: place(3),
                        target: Some(2),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(
                            option_unwrap,
                            vec![GenericArgKind::Type(string_ty)],
                            span,
                        ),
                        args: vec![MirOperand::Move(place(3))],
                        destination: place(4),
                        target: Some(3),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(
                            cstring_new,
                            vec![GenericArgKind::Type(string_ty)],
                            span,
                        ),
                        args: vec![MirOperand::Move(place(4))],
                        destination: place(5),
                        target: Some(4),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(
                            result_unwrap,
                            vec![
                                GenericArgKind::Type(cstring_ty),
                                GenericArgKind::Type(nul_error_ty),
                            ],
                            span,
                        ),
                        args: vec![MirOperand::Move(place(5))],
                        destination: place(6),
                        target: Some(5),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(cstring_into_raw, vec![], span),
                        args: vec![MirOperand::Move(place(6))],
                        destination: place(7),
                        target: Some(6),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(open, vec![], span),
                        args: vec![MirOperand::Copy(place(7)), const_uint(0, span)],
                        destination: place(8),
                        target: Some(7),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(malloc, vec![], span),
                        args: vec![const_uint(4096, span)],
                        destination: place(9),
                        target: Some(8),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(read, vec![], span),
                        args: vec![
                            MirOperand::Copy(place(8)),
                            MirOperand::Copy(place(9)),
                            const_uint(4096, span),
                        ],
                        destination: place(10),
                        target: Some(9),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(write, vec![], span),
                        args: vec![
                            const_uint(1, span),
                            MirOperand::Copy(place(9)),
                            MirOperand::Copy(place(10)),
                        ],
                        destination: place(11),
                        target: Some(10),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(close, vec![], span),
                        args: vec![MirOperand::Copy(place(8))],
                        destination: place(11),
                        target: Some(11),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(free, vec![], span),
                        args: vec![MirOperand::Copy(place(9))],
                        destination: place(0),
                        target: Some(12),
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            },
            MirBasicBlock {
                statements: vec![],
                terminator: MirTerminator {
                    kind: TerminatorKind::Return,
                    span,
                },
            },
        ];
        Body::new(blocks, locals, 0, vec![], None, span)
    }
}

fn main() {
    generate::<State>();
}
