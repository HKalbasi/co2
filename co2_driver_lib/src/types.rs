use co2_hir_mir::{FuncSig, MirModule, Type as HirType};
use rustc_public_generative as rustc_gen;
use rustc_public_generative::rustc_public::{
    mir::Mutability,
    ty::{AdtDef, FnDef, GenericArgKind, GenericArgs, IntTy, RigidTy, Ty, UintTy},
};

#[derive(Clone, Copy, Debug)]
pub struct CompileMode {
    pub no_main: bool,
    pub function_abi: rustc_gen::FunctionAbi,
    pub function_no_mangle: bool,
    pub function_is_unsafe: bool,
}

impl CompileMode {
    pub const RUST: Self = Self {
        no_main: false,
        function_abi: rustc_gen::FunctionAbi::Rust,
        function_no_mangle: false,
        function_is_unsafe: false,
    };

    pub const C: Self = Self {
        no_main: true,
        function_abi: rustc_gen::FunctionAbi::C,
        function_no_mangle: true,
        function_is_unsafe: false,
    };
}

pub(crate) fn hir_sig_from_func_sig(
    sig: &FuncSig,
    module: &MirModule,
    deps: &rustc_gen::DependencyInfo,
    abi: rustc_gen::FunctionAbi,
    is_unsafe: bool,
    span: rustc_gen::rustc_public::ty::Span,
) -> rustc_gen::FunctionSignature {
    rustc_gen::FunctionSignature {
        inputs: sig
            .params
            .iter()
            .map(|t| hir_ty_from_type(t, Some(module), deps, span))
            .collect(),
        output: hir_ty_from_type(&sig.ret, Some(module), deps, span),
        abi,
        is_unsafe,
    }
}

pub(crate) fn mir_ty_from_type(
    ty: &HirType,
    module: Option<&MirModule>,
    deps: &rustc_gen::DependencyInfo,
) -> Ty {
    match ty {
        HirType::Void => Ty::new_tuple(&[]),
        HirType::Int => Ty::signed_ty(IntTy::I32),
        HirType::Char => Ty::signed_ty(IntTy::I8),
        HirType::Ptr(inner) => Ty::new_ptr(mir_ty_from_type(inner, module, deps), Mutability::Mut),
        HirType::Array(inner) => Ty::new_ptr(mir_ty_from_type(inner, module, deps), Mutability::Mut),
        HirType::RustPath(path) => mir_ty_from_rust_path(path, module, deps),
    }
}

pub(crate) fn hir_ty_from_type(
    ty: &HirType,
    module: Option<&MirModule>,
    deps: &rustc_gen::DependencyInfo,
    span: rustc_gen::rustc_public::ty::Span,
) -> rustc_gen::HirTy {
    match ty {
        HirType::Void => rustc_gen::HirTy::new_tuple(vec![], span),
        HirType::Int => rustc_gen::HirTy::signed_ty(IntTy::I32, span),
        HirType::Char => rustc_gen::HirTy::signed_ty(IntTy::I8, span),
        HirType::Ptr(inner) => rustc_gen::HirTy::new_ptr(
            hir_ty_from_type(inner, module, deps, span),
            Mutability::Mut,
            span,
        ),
        HirType::Array(inner) => rustc_gen::HirTy::new_ptr(
            hir_ty_from_type(inner, module, deps, span),
            Mutability::Mut,
            span,
        ),
        HirType::RustPath(path) => hir_ty_from_rust_path(path, module, deps, span),
    }
}

pub(crate) fn mir_ty_from_rust_path(
    path: &co2_parser::RustPath,
    module: Option<&MirModule>,
    deps: &rustc_gen::DependencyInfo,
) -> Ty {
    let base = rust_path_base_string(path);
    if let Some(prim) = primitive_mir_ty(&base) {
        return prim;
    }

    let adt = dep_adt(deps, &base);
    let mut generic_args = rust_path_generic_args(path)
        .into_iter()
        .map(|arg| GenericArgKind::Type(mir_ty_from_rust_path(&arg, module, deps)))
        .collect::<Vec<_>>();
    if (base == "std::vec::Vec" || base == "alloc::vec::Vec" || base.ends_with("::Vec"))
        && generic_args.len() == 1
    {
        let global = dep_adt_any(deps, &["alloc::alloc::Global", "std::alloc::Global"]);
        generic_args.push(GenericArgKind::Type(Ty::from_rigid_kind(RigidTy::Adt(
            global,
            GenericArgs(vec![]),
        ))));
    }
    Ty::from_rigid_kind(RigidTy::Adt(adt, GenericArgs(generic_args)))
}

pub(crate) fn hir_ty_from_rust_path(
    path: &co2_parser::RustPath,
    module: Option<&MirModule>,
    deps: &rustc_gen::DependencyInfo,
    span: rustc_gen::rustc_public::ty::Span,
) -> rustc_gen::HirTy {
    let base = rust_path_base_string(path);
    if let Some(prim) = primitive_hir_ty(&base, span) {
        return prim;
    }

    let adt = dep_adt(deps, &base);
    let mut generic_args = rust_path_generic_args(path)
        .into_iter()
        .map(|arg| {
            rustc_gen::HirGenericArg::Ty(hir_ty_from_rust_path(&arg, module, deps, span))
        })
        .collect::<Vec<_>>();
    if (base == "std::vec::Vec" || base == "alloc::vec::Vec" || base.ends_with("::Vec"))
        && generic_args.len() == 1
    {
        let global = dep_adt_any(deps, &["alloc::alloc::Global", "std::alloc::Global"]);
        generic_args.push(rustc_gen::HirGenericArg::Ty(rustc_gen::HirTy::adt(
            global,
            vec![],
            span,
        )));
    }
    rustc_gen::HirTy::adt(adt, generic_args, span)
}

fn rust_path_base_string(path: &co2_parser::RustPath) -> String {
    path.segments
        .iter()
        .filter_map(|seg| match &seg.0 {
            co2_parser::RustPathSegment::Ident(s) => Some(s.clone()),
            co2_parser::RustPathSegment::Generics(_) => None,
        })
        .collect::<Vec<_>>()
        .join("::")
}

pub(crate) fn rust_path_generic_args(path: &co2_parser::RustPath) -> Vec<co2_parser::RustPath> {
    for seg in &path.segments {
        if let co2_parser::RustPathSegment::Generics(args) = &seg.0 {
            return args.iter().map(|arg| arg.0.clone()).collect();
        }
    }
    Vec::new()
}

fn primitive_mir_ty(name: &str) -> Option<Ty> {
    match name {
        "u8" => Some(Ty::unsigned_ty(UintTy::U8)),
        "i8" => Some(Ty::signed_ty(IntTy::I8)),
        "u32" => Some(Ty::unsigned_ty(UintTy::U32)),
        "i32" => Some(Ty::signed_ty(IntTy::I32)),
        "usize" => Some(Ty::usize_ty()),
        "isize" => Some(Ty::signed_ty(IntTy::Isize)),
        _ => None,
    }
}

fn primitive_hir_ty(name: &str, span: rustc_gen::rustc_public::ty::Span) -> Option<rustc_gen::HirTy> {
    match name {
        "u8" => Some(rustc_gen::HirTy::unsigned_ty(UintTy::U8, span)),
        "i8" => Some(rustc_gen::HirTy::signed_ty(IntTy::I8, span)),
        "u32" => Some(rustc_gen::HirTy::unsigned_ty(UintTy::U32, span)),
        "i32" => Some(rustc_gen::HirTy::signed_ty(IntTy::I32, span)),
        "usize" => Some(rustc_gen::HirTy::usize_ty(span)),
        "isize" => Some(rustc_gen::HirTy::signed_ty(IntTy::Isize, span)),
        _ => None,
    }
}

pub(crate) fn dep_fn(deps: &rustc_gen::DependencyInfo, path: &str) -> FnDef {
    if let Some(found) = find_dep_fn(deps, path) {
        if std::env::var("CO2_DEBUG_DEP").is_ok() {
            eprintln!("dep_fn resolved: {path}");
        }
        return found;
    }

    if let Some(last) = path.rsplit("::").next() {
        if let Some(found) = deps
            .functions
            .iter()
            .find(|f| f.path.ends_with(&format!("::{last}")) && f.fn_def.is_some())
            .and_then(|f| f.fn_def)
        {
            if std::env::var("CO2_DEBUG_DEP").is_ok() {
                eprintln!("dep_fn fallback resolved by suffix: {path} -> ::{last}");
            }
            return found;
        }
    }

    panic!("missing dependency function: {path}");
}

pub(crate) fn dep_fn_any(deps: &rustc_gen::DependencyInfo, paths: &[&str]) -> FnDef {
    for path in paths {
        if let Some(found) = find_dep_fn(deps, path) {
            return found;
        }
    }
    if let Some(last) = paths.iter().find_map(|p| p.rsplit("::").next()) {
        if let Some(found) = deps
            .functions
            .iter()
            .find(|f| {
                f.path.ends_with(&format!("::{last}"))
                    && f.fn_def.is_some()
                    && paths.iter().any(|p| {
                        let required_segments =
                            p.split("::").filter(|s| !s.is_empty()).collect::<Vec<_>>();
                        required_segments.iter().all(|seg| f.path.contains(seg))
                    })
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
            paths.iter().any(|p| {
                let last = p.rsplit("::").next().unwrap_or(p);
                f.path.contains(last)
            })
        })
        .map(|f| format!("{} (fn_def={})", f.path, f.fn_def.is_some()))
        .collect::<Vec<_>>();
    similar.sort();
    similar.truncate(40);
    let joined = paths.join(", ");
    panic!(
        "missing dependency function (any of): {joined}\nexample matches:\n{}",
        similar.join("\n")
    );
}

fn find_dep_fn(deps: &rustc_gen::DependencyInfo, path: &str) -> Option<FnDef> {
    if let Some(found) = deps
        .functions
        .iter()
        .find(|f| f.path == path && f.fn_def.is_some())
        .and_then(|f| f.fn_def)
    {
        return Some(found);
    }

    if let Some(found) = deps
        .functions
        .iter()
        .find(|f| {
            f.path.ends_with(path)
                && f.fn_def.is_some()
                && !f.path.contains("::{closure")
                && !f.path.contains("{{")
        })
        .and_then(|f| f.fn_def)
    {
        return Some(found);
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
            return Some(found);
        }
    }

    None
}

pub(crate) fn dep_adt(deps: &rustc_gen::DependencyInfo, path: &str) -> AdtDef {
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
            .find(|t| t.path.ends_with(&format!("::{last}")))
            .map(|t| t.adt)
        {
            return found;
        }
    }

    panic!("missing dependency type: {path}");
}

pub(crate) fn dep_adt_any(deps: &rustc_gen::DependencyInfo, paths: &[&str]) -> AdtDef {
    for path in paths {
        if let Some(found) = deps.types.iter().find(|t| t.path == *path).map(|t| t.adt) {
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
    }
    panic!("missing dependency type (any of): {}", paths.join(", "));
}
