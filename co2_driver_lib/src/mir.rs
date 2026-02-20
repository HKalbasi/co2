use std::collections::HashMap;

use co2_hir_mir::{
    Callee as HirCallee, Function as HirFunction, LocalDecl as HirLocalDecl, MirModule,
    MirOp as HirOp, Operand as HirOperand, Type as HirType,
};
use rustc_public_generative as rustc_gen;
use rustc_public_generative::rustc_public::{
    DefId,
    mir::{
        BasicBlock as MirBasicBlock, Body, BorrowKind, CastKind, ConstOperand,
        LocalDecl as MirLocalDecl, MutBorrowKind, Mutability, Operand as MirOperand,
        Place as MirPlace, Rvalue, Statement as MirStatement, StatementKind as MirStatementKind,
        Terminator as MirTerminator, TerminatorKind, UnwindAction,
    },
    ty::{FnDef, GenericArgKind, GenericArgs, IntTy, MirConst, Region, RegionKind, RigidTy, Span, Ty, UintTy},
};

use crate::types::{
    CompileMode, dep_adt_any, dep_fn, dep_fn_any, mir_ty_from_rust_path, mir_ty_from_type,
    rust_path_generic_args,
};

pub(crate) fn build_mir_for_def(
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
    local_fn_defs: &HashMap<String, FnDef>,
    ctx: &rustc_gen::HirStructureCtx,
    file_id: rustc_gen::FileId,
    mode: CompileMode,
    def: DefId,
) -> Body {
    let func = module
        .functions
        .iter()
        .find(|f| local_fn_defs.get(&f.name).is_some_and(|fn_def| fn_def.0 == def))
        .unwrap_or_else(|| panic!("missing function definition for def {def:?}"));
    let is_rust_entry_main = mode.no_main && func.name == "main";
    build_mir(
        func,
        module,
        deps,
        local_fn_defs,
        ctx,
        file_id,
        mode,
        is_rust_entry_main,
    )
}

fn build_mir(
    func: &HirFunction,
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
    local_fn_defs: &HashMap<String, FnDef>,
    ctx: &rustc_gen::HirStructureCtx,
    file_id: rustc_gen::FileId,
    mode: CompileMode,
    is_rust_entry_main: bool,
) -> Body {
    let span = ctx.span_in_file(file_id, 0, 0);
    let exit_fn = if is_rust_entry_main {
        Some(dep_fn_any(deps, &["std::process::exit", "core::process::exit"]))
    } else {
        None
    };

    let mut locals = Vec::new();
    for (idx, local) in func.locals.iter().enumerate() {
        let ty = if is_rust_entry_main && idx == 0 {
            Ty::new_tuple(&[])
        } else {
            mir_ty_from_type(&local.ty, Some(module), deps)
        };
        locals.push(MirLocalDecl {
            ty,
            span,
            mutability: Mutability::Mut,
        });
    }

    let mut blocks = Vec::new();
    let mut stmts = Vec::new();
    let mut extra_locals: Vec<MirLocalDecl> = Vec::new();
    let exit_code_local = if is_rust_entry_main {
        let i32_ty = Ty::signed_ty(IntTy::I32);
        let local = locals.len() + extra_locals.len();
        extra_locals.push(MirLocalDecl {
            ty: i32_ty,
            span,
            mutability: Mutability::Mut,
        });
        let zero = MirConst::try_from_uint(0, UintTy::U32).expect("failed to build zero const");
        stmts.push(MirStatement {
            kind: MirStatementKind::Assign(
                place(local),
                Rvalue::Cast(
                    CastKind::IntToInt,
                    MirOperand::Constant(ConstOperand {
                        span,
                        user_ty: None,
                        const_: zero,
                    }),
                    i32_ty,
                ),
            ),
            span,
        });
        Some(local)
    } else {
        None
    };

    for op in &func.ops {
        match op {
            HirOp::Assign { dst, src } => {
                if is_rust_entry_main && *dst == 0 {
                    let value_op = lower_operand(
                        src,
                        &locals,
                        &mut extra_locals,
                        deps,
                        module,
                        &mut blocks,
                        &mut stmts,
                        ctx,
                        file_id,
                        mode,
                    );
                    stmts.push(MirStatement {
                        kind: MirStatementKind::Assign(
                            place(exit_code_local.expect("missing exit local")),
                            Rvalue::Use(value_op),
                        ),
                        span,
                    });
                    continue;
                }
                let rvalue = Rvalue::Use(lower_operand(
                    src,
                    &locals,
                    &mut extra_locals,
                    deps,
                    module,
                    &mut blocks,
                    &mut stmts,
                    ctx,
                    file_id,
                    mode,
                ));
                stmts.push(MirStatement {
                    kind: MirStatementKind::Assign(place(*dst), rvalue),
                    span,
                });
            }
            HirOp::Call {
                func: callee,
                args,
                dest,
            } => {
                let (func_op, arg_ops) = lower_call(
                    callee,
                    args,
                    &func.locals,
                    &locals,
                    &mut extra_locals,
                    deps,
                    module,
                    local_fn_defs,
                    &mut blocks,
                    &mut stmts,
                    ctx,
                    file_id,
                    span,
                    mode,
                );
                let dest_place = dest.map(place).unwrap_or_else(|| {
                    let idx = locals.len() + extra_locals.len();
                    let ret_ty = call_return_ty(callee, module, deps);
                    extra_locals.push(MirLocalDecl {
                        ty: ret_ty,
                        span,
                        mutability: Mutability::Mut,
                    });
                    place(idx)
                });
                emit_call_block(&mut blocks, &mut stmts, span, func_op, arg_ops, dest_place);
            }
            HirOp::Return => {
                if is_rust_entry_main {
                    blocks.push(MirBasicBlock {
                        statements: std::mem::take(&mut stmts),
                        terminator: MirTerminator {
                            kind: TerminatorKind::Call {
                                func: fn_const_operand(exit_fn.expect("missing exit fn"), vec![], span),
                                args: vec![MirOperand::Copy(place(
                                    exit_code_local.expect("missing exit local"),
                                ))],
                                destination: place(0),
                                target: None,
                                unwind: UnwindAction::Continue,
                            },
                            span,
                        },
                    });
                } else {
                    blocks.push(MirBasicBlock {
                        statements: std::mem::take(&mut stmts),
                        terminator: MirTerminator {
                            kind: TerminatorKind::Return,
                            span,
                        },
                    });
                }
            }
        }
    }

    if !stmts.is_empty() {
        if is_rust_entry_main {
            blocks.push(MirBasicBlock {
                statements: std::mem::take(&mut stmts),
                terminator: MirTerminator {
                    kind: TerminatorKind::Call {
                        func: fn_const_operand(exit_fn.expect("missing exit fn"), vec![], span),
                        args: vec![MirOperand::Copy(place(
                            exit_code_local.expect("missing exit local"),
                        ))],
                        destination: place(0),
                        target: None,
                        unwind: UnwindAction::Continue,
                    },
                    span,
                },
            });
        } else {
            blocks.push(MirBasicBlock {
                statements: std::mem::take(&mut stmts),
                terminator: MirTerminator {
                    kind: TerminatorKind::Return,
                    span,
                },
            });
        }
    }

    locals.extend(extra_locals);

    Body::new(blocks, locals, 0, vec![], None, span)
}

fn place(local: usize) -> MirPlace {
    MirPlace {
        local,
        projection: vec![],
    }
}

fn emit_call_block(
    blocks: &mut Vec<MirBasicBlock>,
    stmts: &mut Vec<MirStatement>,
    span: Span,
    func: MirOperand,
    args: Vec<MirOperand>,
    destination: MirPlace,
) {
    let next = blocks.len() + 1;
    blocks.push(MirBasicBlock {
        statements: std::mem::take(stmts),
        terminator: MirTerminator {
            kind: TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(next),
                unwind: UnwindAction::Continue,
            },
            span,
        },
    });
}

fn infer_generic_args_for_call(
    path: &str,
    args: &[HirOperand],
    hir_locals: &[HirLocalDecl],
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
) -> Vec<GenericArgKind> {
    if path.ends_with("::Option::unwrap") || path.ends_with("::option::Option::unwrap") {
        if let Some(arg_ty) = hir_operand_type(args.first(), hir_locals) {
            return generic_args_from_type(arg_ty, module, deps);
        }
    }

    if path.ends_with("::Result::unwrap") || path.ends_with("::result::Result::unwrap") {
        if let Some(arg_ty) = hir_operand_type(args.first(), hir_locals) {
            return generic_args_from_type(arg_ty, module, deps);
        }
    }

    if path.ends_with("::Iterator::nth") || path.ends_with("::Iterator::next") {
        if let Some(arg_ty) = hir_operand_type(args.first(), hir_locals) {
            return vec![GenericArgKind::Type(mir_ty_from_type(arg_ty, Some(module), deps))];
        }
    }

    if path.ends_with("::CString::new") {
        if let Some(arg_ty) = hir_operand_type(args.first(), hir_locals) {
            return vec![GenericArgKind::Type(mir_ty_from_type(arg_ty, Some(module), deps))];
        }
    }

    if path.ends_with("::fs::read") || path.ends_with("::std::fs::read") {
        if let Some(arg_ty) = hir_operand_type(args.first(), hir_locals) {
            return vec![GenericArgKind::Type(mir_ty_from_type(arg_ty, Some(module), deps))];
        }
    }

    if path.ends_with("::Vec::as_ptr")
        || path.ends_with("::Vec::as_mut_ptr")
        || path.ends_with("::Vec::len")
    {
        if let Some(arg_ty) = hir_operand_type(args.first(), hir_locals) {
            return vec_method_generic_args(arg_ty, module, deps);
        }
    }

    Vec::new()
}

fn hir_operand_type<'a>(
    operand: Option<&'a HirOperand>,
    hir_locals: &'a [HirLocalDecl],
) -> Option<&'a HirType> {
    let HirOperand::Local(local) = operand? else {
        return None;
    };
    hir_locals.get(*local).map(|l| &l.ty)
}

fn generic_args_from_type(
    ty: &HirType,
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
) -> Vec<GenericArgKind> {
    let HirType::RustPath(path) = ty else {
        return Vec::new();
    };
    rust_path_generic_args(path)
        .into_iter()
        .map(|arg| GenericArgKind::Type(mir_ty_from_rust_path(&arg, Some(module), deps)))
        .collect()
}

fn vec_method_generic_args(
    ty: &HirType,
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
) -> Vec<GenericArgKind> {
    let mut args = generic_args_from_type(ty, module, deps);
    if args.len() == 1 {
        let global = dep_adt_any(deps, &["alloc::alloc::Global", "std::alloc::Global"]);
        let global_ty = Ty::from_rigid_kind(RigidTy::Adt(global, GenericArgs(vec![])));
        args.push(GenericArgKind::Type(global_ty));
    }
    args
}

enum AutorefKind {
    Shared,
    Mut,
}

fn autoref_kind_for_path(path: &str) -> Option<AutorefKind> {
    if path.ends_with("::Iterator::nth") || path.ends_with("::Iterator::next") {
        return Some(AutorefKind::Mut);
    }

    if path.ends_with("::CString::as_ptr")
        || path.ends_with("::String::as_ptr")
        || path.ends_with("::String::as_str")
        || path.ends_with("::Vec::as_ptr")
        || path.ends_with("::Vec::len")
    {
        return Some(AutorefKind::Shared);
    }

    if path.ends_with("::Vec::as_mut_ptr") {
        return Some(AutorefKind::Mut);
    }

    None
}

#[allow(clippy::too_many_arguments)]
fn autoref_call_arg(
    path: &str,
    arg_index: usize,
    arg: &HirOperand,
    hir_locals: &[HirLocalDecl],
    locals: &[MirLocalDecl],
    extra_locals: &mut Vec<MirLocalDecl>,
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
    stmts: &mut Vec<MirStatement>,
    span: Span,
) -> Option<MirOperand> {
    if arg_index != 0 {
        return None;
    }
    let kind = autoref_kind_for_path(path)?;
    let HirOperand::Local(local) = arg else {
        return None;
    };
    let hir_ty = &hir_locals.get(*local)?.ty;
    let base_ty = mir_ty_from_type(hir_ty, Some(module), deps);
    let (ref_ty, borrow_kind) = match kind {
        AutorefKind::Shared => (
            Ty::new_ref(
                Region {
                    kind: RegionKind::ReErased,
                },
                base_ty,
                Mutability::Not,
            ),
            BorrowKind::Shared,
        ),
        AutorefKind::Mut => (
            Ty::new_ref(
                Region {
                    kind: RegionKind::ReErased,
                },
                base_ty,
                Mutability::Mut,
            ),
            BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            },
        ),
    };

    let ref_local = locals.len() + extra_locals.len();
    extra_locals.push(MirLocalDecl {
        ty: ref_ty,
        span,
        mutability: Mutability::Not,
    });
    stmts.push(MirStatement {
        kind: MirStatementKind::Assign(
            place(ref_local),
            Rvalue::Ref(
                Region {
                    kind: RegionKind::ReErased,
                },
                borrow_kind,
                place(*local),
            ),
        ),
        span,
    });
    Some(MirOperand::Move(place(ref_local)))
}

#[allow(clippy::too_many_arguments)]
fn lower_call(
    callee: &HirCallee,
    args: &[HirOperand],
    hir_locals: &[HirLocalDecl],
    locals: &[MirLocalDecl],
    extra_locals: &mut Vec<MirLocalDecl>,
    deps: &rustc_gen::DependencyInfo,
    module: &MirModule,
    local_fn_defs: &HashMap<String, FnDef>,
    blocks: &mut Vec<MirBasicBlock>,
    stmts: &mut Vec<MirStatement>,
    ctx: &rustc_gen::HirStructureCtx,
    file_id: rustc_gen::FileId,
    span: Span,
    mode: CompileMode,
) -> (MirOperand, Vec<MirOperand>) {
    let (func_def, path) = match callee {
        HirCallee::Path(path) => {
            if let Some(item) = local_fn_defs.get(path) {
                if std::env::var("CO2_DEBUG_CALLS").is_ok() {
                    eprintln!("call {path}: resolved as defined item");
                }
                (*item, path.as_str())
            } else {
                if std::env::var("CO2_DEBUG_CALLS").is_ok() {
                    eprintln!("call {path}: resolving from deps");
                }
                (resolve_dep_fn_for_path(deps, path), path.as_str())
            }
        }
    };

    let generic_args = infer_generic_args_for_call(path, args, hir_locals, module, deps);
    let func_op = fn_const_operand(func_def, generic_args, span);
    let mut arg_ops = Vec::new();
    for (idx, arg) in args.iter().enumerate() {
        if path.ends_with("::Iterator::nth") && idx == 1 {
            if let HirOperand::ConstInt(v, sp) = arg {
                let arg_span = ctx.span_in_file(file_id, sp.start as u32, sp.end as u32);
                let c = MirConst::try_from_uint(*v as u128, UintTy::Usize)
                    .expect("failed to build usize const");
                arg_ops.push(MirOperand::Constant(ConstOperand {
                    span: arg_span,
                    user_ty: None,
                    const_: c,
                }));
                continue;
            }
        }
        if let Some(auto_ref) = autoref_call_arg(
            path,
            idx,
            arg,
            hir_locals,
            locals,
            extra_locals,
            module,
            deps,
            stmts,
            span,
        ) {
            arg_ops.push(auto_ref);
            continue;
        }
        if let HirOperand::Local(local) = arg {
            arg_ops.push(MirOperand::Move(place(*local)));
            continue;
        }
        arg_ops.push(lower_operand(
            arg,
            locals,
            extra_locals,
            deps,
            module,
            blocks,
            stmts,
            ctx,
            file_id,
            mode,
        ));
    }

    (func_op, arg_ops)
}

fn resolve_dep_fn_for_path(deps: &rustc_gen::DependencyInfo, path: &str) -> FnDef {
    if path == "printf" || path.ends_with("::printf") {
        return dep_fn_any(deps, &["libc::printf", "libc::unix::printf"]);
    }
    if path.ends_with("::Option::unwrap") || path.ends_with("::option::Option::unwrap") {
        return dep_fn_any(
            deps,
            &[
                "core::option::Option::unwrap",
                "std::option::Option::unwrap",
            ],
        );
    }
    if path.ends_with("::Result::unwrap") || path.ends_with("::result::Result::unwrap") {
        return dep_fn_any(
            deps,
            &[
                "core::result::Result::unwrap",
                "std::result::Result::unwrap",
            ],
        );
    }
    if path.ends_with("::Vec::as_mut_ptr") {
        return dep_fn_any(
            deps,
            &["alloc::vec::Vec::as_mut_ptr", "std::vec::Vec::as_mut_ptr"],
        );
    }
    if path.ends_with("::Vec::as_ptr") {
        return dep_fn_any(deps, &["alloc::vec::Vec::as_ptr", "std::vec::Vec::as_ptr"]);
    }
    if path.ends_with("::Vec::len") {
        return dep_fn_any(deps, &["alloc::vec::Vec::len", "std::vec::Vec::len"]);
    }
    dep_fn(deps, path)
}

fn call_return_ty(callee: &HirCallee, module: &MirModule, deps: &rustc_gen::DependencyInfo) -> Ty {
    match callee {
        HirCallee::Path(path) => {
            if path == "printf" || path.ends_with("::printf") {
                return Ty::signed_ty(IntTy::I32);
            }
            if let Some(f) = module.functions.iter().find(|f| f.name == *path) {
                return mir_ty_from_type(&f.sig.ret, Some(module), deps);
            }
            if let Some(f) = module.externs.iter().find(|f| f.name == *path) {
                return mir_ty_from_type(&f.sig.ret, Some(module), deps);
            }
            Ty::new_tuple(&[])
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_operand(
    operand: &HirOperand,
    locals: &[MirLocalDecl],
    extra_locals: &mut Vec<MirLocalDecl>,
    deps: &rustc_gen::DependencyInfo,
    _module: &MirModule,
    blocks: &mut Vec<MirBasicBlock>,
    stmts: &mut Vec<MirStatement>,
    ctx: &rustc_gen::HirStructureCtx,
    file_id: rustc_gen::FileId,
    mode: CompileMode,
) -> MirOperand {
    match operand {
        HirOperand::Local(l) => MirOperand::Copy(place(*l)),
        HirOperand::ConstInt(v, sp) => {
            let span = ctx.span_in_file(file_id, sp.start as u32, sp.end as u32);
            let c = MirConst::try_from_uint(*v as u128, UintTy::U32)
                .expect("failed to build int const");
            let const_op = MirOperand::Constant(ConstOperand {
                span,
                user_ty: None,
                const_: c,
            });
            let tmp_local = locals.len() + extra_locals.len();
            let i32_ty = Ty::signed_ty(IntTy::I32);
            extra_locals.push(MirLocalDecl {
                ty: i32_ty,
                span,
                mutability: Mutability::Mut,
            });
            stmts.push(MirStatement {
                kind: MirStatementKind::Assign(
                    place(tmp_local),
                    Rvalue::Cast(CastKind::IntToInt, const_op, i32_ty),
                ),
                span,
            });
            MirOperand::Copy(place(tmp_local))
        }
        HirOperand::ConstStr(s, sp) => {
            let span = ctx.span_in_file(file_id, sp.start as u32, sp.end as u32);
            let mut value = s.clone();
            if !value.ends_with('\0') {
                value.push('\0');
            }
            let str_const = MirOperand::Constant(ConstOperand {
                span,
                user_ty: None,
                const_: MirConst::from_str(&value),
            });
            let as_ptr = dep_fn_any(deps, &["core::str::as_ptr", "std::str::as_ptr"]);
            let u8_ty = Ty::unsigned_ty(UintTy::U8);
            let ptr_u8_ty = Ty::new_ptr(u8_ty, Mutability::Not);
            let ptr_u8_local = locals.len() + extra_locals.len();
            extra_locals.push(MirLocalDecl {
                ty: ptr_u8_ty,
                span,
                mutability: Mutability::Mut,
            });
            emit_call_block(
                blocks,
                stmts,
                span,
                fn_const_operand(as_ptr, vec![], span),
                vec![str_const],
                place(ptr_u8_local),
            );

            let i8_ty = Ty::signed_ty(IntTy::I8);
            let ptr_i8_ty = Ty::new_ptr(
                i8_ty,
                if mode.no_main {
                    Mutability::Not
                } else {
                    Mutability::Mut
                },
            );
            let ptr_i8_local = locals.len() + extra_locals.len();
            extra_locals.push(MirLocalDecl {
                ty: ptr_i8_ty,
                span,
                mutability: Mutability::Mut,
            });
            stmts.push(MirStatement {
                kind: MirStatementKind::Assign(
                    place(ptr_i8_local),
                    Rvalue::Cast(
                        CastKind::PtrToPtr,
                        MirOperand::Copy(place(ptr_u8_local)),
                        ptr_i8_ty,
                    ),
                ),
                span,
            });

            MirOperand::Copy(place(ptr_i8_local))
        }
    }
}

fn fn_const_operand(fn_def: FnDef, generic_args: Vec<GenericArgKind>, span: Span) -> MirOperand {
    let fn_ty = Ty::from_rigid_kind(RigidTy::FnDef(fn_def, GenericArgs(generic_args)));
    let c = MirConst::try_new_zero_sized(fn_ty).expect("failed to build fn const");
    MirOperand::Constant(ConstOperand {
        span,
        user_ty: None,
        const_: c,
    })
}
