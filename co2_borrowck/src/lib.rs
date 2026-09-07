#![feature(rustc_private)]

extern crate rustc_data_structures;

pub mod check;
pub(crate) mod facts;

pub use check::{BorrowckWarning, check};
