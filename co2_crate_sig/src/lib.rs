#![feature(rustc_private)]

mod ctx;
mod lowering;
mod mir;
mod resolver;
mod span;
mod struct_manager;
mod ty;

pub(crate) use ctx::CrateSigCtx;

pub use lowering::lower_crate_sig;
pub use mir::MirOwnerInfo;
pub use resolver::Resolver;
