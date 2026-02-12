mod ir;
mod lower;
mod resolver;

pub use ir::{
    Callee, ExternFunction, FuncSig, Function, LocalDecl, MirModule, MirOp, Operand, Type,
};
pub use lower::parse_and_lower;
