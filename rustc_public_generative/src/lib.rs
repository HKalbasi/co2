#![feature(rustc_private)]

//! rustc_public_generative
//!
//! This crate provides a `generate` entrypoint that runs `rustc_driver`
//! but injects a synthetic crate produced by user code.

use std::{any::Any, path::PathBuf};

use rustc_middle::ty::TyCtxt;
use rustc_public::{
    DefId,
    ty::{AdtDef, FnDef},
};

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hashes;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_middle;
pub extern crate rustc_public;
extern crate rustc_public_bridge;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

mod hir_structure;
mod hir_ty;
mod internal;

pub use hir_structure::{
    ForeignModItem, FunctionAbi, FunctionSignature, HirAdtKind, HirImplItem, HirImplItemKind,
    HirModule, HirModuleItem, HirSelfKind, HirStructure, StructField, AdtRepr,
};
pub use hir_ty::{HirGenericArg, HirLifetime, HirTy, HirTyConst, HirTyKind};

/// Summary of crates loaded as dependencies by rustc.
#[derive(Debug, Clone, Default)]
pub struct DependencyInfo {
    pub crates: Vec<DependencyCrate>,
    pub functions: Vec<DependencyFunction>,
    pub values: Vec<DependencyValue>,
    pub types: Vec<DependencyType>,
    pub traits: Vec<DependencyTrait>,
}

#[derive(Debug, Clone)]
pub struct DependencyCrate {
    pub name: String,
    pub disambiguator: String,
}

#[derive(Debug, Clone)]
pub struct DependencyFunction {
    pub path: String,
    pub def_path_hash_hi: u64,
    pub def_path_hash_lo: u64,
    pub fn_def: Option<FnDef>,
}

#[derive(Debug, Clone)]
pub enum DependencyConstValue {
    Bool(bool),
    Char(char),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Isize(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    Usize(u64),
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone)]
pub enum DependencyValueKind {
    Def(DefId),
    ConstDef(DefId),
}

#[derive(Debug, Clone)]
pub struct DependencyValue {
    pub kind: DependencyValueKind,
    pub path: String,
    pub def_path_hash_hi: u64,
    pub def_path_hash_lo: u64,
}

#[derive(Debug, Clone)]
pub struct DependencyType {
    pub adt: AdtDef,
    pub path: String,
    pub def_path_hash_hi: u64,
    pub def_path_hash_lo: u64,
}

#[derive(Debug, Clone)]
pub struct DependencyTrait {
    pub def_id: DefId,
    pub path: String,
    pub def_path_hash_hi: u64,
    pub def_path_hash_lo: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(u32);

pub struct HirStructureCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    inner: internal::Context,
}

impl<'tcx> std::fmt::Debug for HirStructureCtx<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HirStructureCtx").finish()
    }
}

impl HirStructureCtx<'_> {
    pub fn dependencies(&self) -> DependencyInfo {
        internal::collect_dependency_info(self.tcx)
    }

    pub fn add_custom_file(&self, path: impl Into<PathBuf>, contents: impl Into<String>) -> FileId {
        let result = self.inner.add_custom_file(path, contents);
        self.inner.register_with_source_map(self.tcx);
        result
    }

    pub fn span_in_file(&self, file: FileId, lo: u32, hi: u32) -> rustc_public::ty::Span {
        self.inner.span_in_file(file, lo, hi)
    }

    pub fn root_crate_def_id(&self) -> DefId {
        internal::root_crate_def_id(self.tcx)
    }

    pub fn allocate_def_id(&self, parent: DefId, data: DefData) -> DefId {
        internal::allocate_def_id(self.tcx, parent, data)
    }

    pub fn dependency_const_value(&self, def_id: DefId) -> Option<DependencyConstValue> {
        internal::dependency_const_value_for_def_id(self.tcx, def_id)
    }
}

pub trait CrateGeneratorState: Sync + Send + Any + Sized {
    fn hir_structure(ctx: HirStructureCtx) -> (Self, HirStructure);
    fn emit_mir(&mut self, ctx: HirStructureCtx, def: DefId) -> rustc_public::mir::Body;
}

pub fn generate<S: CrateGeneratorState>() {
    internal::generate::<S>();
}

pub fn generate_with_args<S: CrateGeneratorState>(args: Vec<String>) {
    internal::generate_with_args::<S>(args);
}

#[derive(Debug)]
pub enum DefData {
    ForeignMod,
    ValueNs(String),
    TypeNs(String),
    LifetimeNs(String),
    Impl,
    AnonConst,
}
