#![feature(rustc_private)]

extern crate rustc_data_structures;

mod allocation;
mod basic_block;
mod build;
mod operand;
mod place;
mod rvalue;

pub use build::build_mir_for_body;
