#![allow(unused)]

mod ir;
mod ir_builder;

pub use ir::BasicBlock;
pub use ir::Instruction;
pub use ir::InstructionPayload;
pub use ir::InstructionType;
pub use ir::Ir;
pub use ir_builder::build_ir;
pub use parser::LiteralValue;
