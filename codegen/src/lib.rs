#![allow(unused)]

mod ir;
mod ir_builder;

pub use ir::BasicBlock;
pub use ir::Instruction;
pub use ir::InstructionId;
pub use ir::InstructionPayload;
pub use ir::Ir;
pub use ir_builder::build_ir_expression;
pub use parser::LiteralValue;
