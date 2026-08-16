#![feature(rustc_private)]

pub mod check;
pub(crate) mod facts;

pub use check::{BorrowckWarning, check};
