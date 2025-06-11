#![allow(unused)]

mod ir;
mod ir2;
mod ir_builder;
mod ir_builder2;

pub use ir::BasicBlock;
pub use ir::Instruction;
pub use ir::InstructionPayload;
pub use ir::Ir;
pub use ir_builder::build_ir;
pub use parser::LiteralValue;
