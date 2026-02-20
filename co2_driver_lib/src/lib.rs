#![feature(rustc_private)]

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use co2_hir_mir::{MirModule, parse_and_lower};
use rustc_public_generative as rustc_gen;
use rustc_public_generative::rustc_public::{
    DefId,
    mir::Body,
    ty::FnDef,
};

mod mir;
mod types;

pub use types::CompileMode;

struct PendingCompile {
    mode: CompileMode,
    source_path: PathBuf,
    source: String,
    module: MirModule,
}

fn pending_compile_cell() -> &'static Mutex<Option<PendingCompile>> {
    static CELL: OnceLock<Mutex<Option<PendingCompile>>> = OnceLock::new();
    CELL.get_or_init(|| Mutex::new(None))
}

struct Co2GeneratorState {
    module: MirModule,
    deps: rustc_gen::DependencyInfo,
    file_id: rustc_gen::FileId,
    mode: CompileMode,
    local_fn_defs: HashMap<String, FnDef>,
}

unsafe impl Send for Co2GeneratorState {}
unsafe impl Sync for Co2GeneratorState {}

impl rustc_gen::CrateGeneratorState for Co2GeneratorState {
    fn hir_structure(ctx: rustc_gen::HirStructureCtx) -> (Self, rustc_gen::HirStructure) {
        let pending = pending_compile_cell()
            .lock()
            .unwrap()
            .take()
            .expect("missing pending compile input");

        let file_id = ctx.add_custom_file(&pending.source_path, pending.source);
        let span = ctx.span_in_file(file_id, 0, 0);
        let deps = ctx.dependencies();
        let root_crate = ctx.root_crate_def_id();

        let mut items = Vec::new();
        let mut local_fn_defs = HashMap::new();

        for func in &pending.module.functions {
            let is_c_entry_main = pending.mode.no_main && func.name == "main";
            let abi = if is_c_entry_main {
                rustc_gen::FunctionAbi::Rust
            } else {
                pending.mode.function_abi
            };
            let is_unsafe = if is_c_entry_main {
                false
            } else {
                pending.mode.function_is_unsafe
            };
            let fn_def = FnDef(ctx.allocate_def_id(
                root_crate,
                rustc_gen::DefData::ValueNs(func.name.clone()),
            ));
            local_fn_defs.insert(func.name.clone(), fn_def);
            let mut sig = types::hir_sig_from_func_sig(
                &func.sig,
                &pending.module,
                &deps,
                abi,
                is_unsafe,
                span,
            );
            if is_c_entry_main {
                sig.output = rustc_gen::HirTy::new_tuple(vec![], span);
            }
            items.push(rustc_gen::HirModuleItem::Function {
                name: func.name.clone(),
                id: fn_def,
                sig,
                no_mangle: if is_c_entry_main {
                    false
                } else {
                    pending.mode.function_no_mangle
                },
                span,
            });
        }

        let foreign_mod = ctx.allocate_def_id(root_crate, rustc_gen::DefData::ForeignMod);
        let mut foreign_items = Vec::new();
        for ext in &pending.module.externs {
            let fn_def = FnDef(ctx.allocate_def_id(
                foreign_mod,
                rustc_gen::DefData::ValueNs(ext.name.clone()),
            ));
            local_fn_defs.insert(ext.name.clone(), fn_def);
            foreign_items.push(rustc_gen::ForeignModItem::ForeignFunction {
                name: ext.name.clone(),
                id: fn_def,
                sig: types::hir_sig_from_func_sig(
                    &ext.sig,
                    &pending.module,
                    &deps,
                    rustc_gen::FunctionAbi::C,
                    true,
                    span,
                ),
                span,
            });
        }
        items.push(rustc_gen::HirModuleItem::ForeignMod {
            id: foreign_mod,
            items: foreign_items,
        });

        (
            Co2GeneratorState {
                module: pending.module,
                deps,
                file_id,
                mode: pending.mode,
                local_fn_defs,
            },
            rustc_gen::HirStructure {
                root: rustc_gen::HirModule { span, items },
            },
        )
    }

    fn emit_mir(&mut self, ctx: rustc_gen::HirStructureCtx, def: DefId) -> Body {
        mir::build_mir_for_def(
            &self.module,
            &self.deps,
            &self.local_fn_defs,
            &ctx,
            self.file_id,
            self.mode,
            def,
        )
    }
}

pub fn compile_co2_file(mode: CompileMode, co2_file: &Path) {
    let src = std::fs::read_to_string(co2_file).expect("failed to read co2 file");
    compile_co2_source(
        mode,
        co2_file.to_path_buf(),
        src,
        std::env::args().collect(),
    );
}

pub fn compile_co2_source(
    mode: CompileMode,
    source_path: PathBuf,
    source: String,
    rustc_args: Vec<String>,
) {
    let parse_source: &'static str = Box::leak(source.clone().into_boxed_str());
    let module = parse_and_lower(source_path.to_string_lossy().into_owned(), parse_source)
        .expect("failed to parse and lower co2");

    *pending_compile_cell().lock().unwrap() = Some(PendingCompile {
        mode,
        source_path,
        source,
        module,
    });

    rustc_gen::generate_with_args::<Co2GeneratorState>(rustc_args);
}
