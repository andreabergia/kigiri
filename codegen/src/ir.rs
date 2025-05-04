use bumpalo::collections::Vec as BumpVec;
use parser::LiteralValue;
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use type_engine::Type;

#[derive(Debug, Clone, PartialEq)]
pub enum InstructionType {
    Const,

    Not,
    Neg,
    BitwiseNot,

    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Exp,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitwiseShl,
    BitwiseShr,
}

impl Display for InstructionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionType::Const => write!(f, "const"),
            InstructionType::Not => write!(f, "not"),
            InstructionType::Neg => write!(f, "neg"),
            InstructionType::BitwiseNot => write!(f, "bitwise_not"),
            InstructionType::Add => write!(f, "add"),
            InstructionType::Sub => write!(f, "sub"),
            InstructionType::Mul => write!(f, "mul"),
            InstructionType::Div => write!(f, "div"),
            InstructionType::Rem => write!(f, "rem"),
            InstructionType::Exp => write!(f, "exp"),
            InstructionType::Eq => write!(f, "eq"),
            InstructionType::Neq => write!(f, "neq"),
            InstructionType::Lt => write!(f, "lt"),
            InstructionType::Lte => write!(f, "lte"),
            InstructionType::Gt => write!(f, "gt"),
            InstructionType::Gte => write!(f, "gte"),
            InstructionType::And => write!(f, "and"),
            InstructionType::Or => write!(f, "or"),
            InstructionType::BitwiseAnd => write!(f, "bitwise_and"),
            InstructionType::BitwiseOr => write!(f, "bitwise_or"),
            InstructionType::BitwiseXor => write!(f, "bitwise_xor"),
            InstructionType::BitwiseShl => write!(f, "bitwise_shl"),
            InstructionType::BitwiseShr => write!(f, "bitwise_shr"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instruction<'a> {
    pub operand_type: Type,
    pub name: &'a str,
    pub instruction_type: InstructionType,
    pub args: BumpVec<'a, &'a Instruction<'a>>,
    pub constant: Option<LiteralValue>,
}

impl Display for Instruction<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {:-10} = {}(",
            self.operand_type.to_string_short(),
            self.name,
            self.instruction_type,
        )?;
        for arg in self.args.iter() {
            write!(f, "{}, ", arg.name)?;
        }
        if let Some(constant) = &self.constant {
            write!(f, "{}, ", constant)?;
        }
        write!(f, ")")
    }
}

pub struct BasicBlock<'a> {
    pub instructions: RefCell<BumpVec<'a, &'a Instruction<'a>>>,
}

impl Display for BasicBlock<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let instructions = self.instructions.borrow();
        for instr in instructions.iter() {
            writeln!(f, "{}", instr)?;
        }
        Ok(())
    }
}

pub struct Ir {
    pub(crate) arena: bumpalo::Bump,
}

impl Ir {
    pub fn new() -> Self {
        Self {
            arena: bumpalo::Bump::new(),
        }
    }

    pub fn instruction<'s>(
        &'s self,
        operand_type: Type,
        name: &str,
        instruction_type: InstructionType,
        args: impl IntoIterator<Item = &'s Instruction<'s>>,
        constant: Option<LiteralValue>,
    ) -> &'s Instruction<'s> {
        self.arena.alloc(Instruction {
            operand_type,
            name: self.arena.alloc_str(name),
            instruction_type,
            args: BumpVec::from_iter_in(args, &self.arena),
            constant,
        })
    }

    pub fn basic_block(&self) -> &BasicBlock {
        self.arena.alloc(BasicBlock {
            instructions: RefCell::new(BumpVec::new_in(&self.arena)),
        })
    }
}
