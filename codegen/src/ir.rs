use bumpalo::collections::Vec as BumpVec;
use parser::{BinaryOperator, LiteralValue, UnaryOperator};
use semantic_analysis::Type;
use std::cell::RefCell;
use std::fmt::{Binary, Display, Formatter};

#[derive(Debug, Clone, PartialEq)]
pub enum InstructionType {
    Ret,

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
            InstructionType::Ret => write!(f, "ret"),
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

#[derive(Debug, PartialEq)]
pub enum InstructionPayload<'a> {
    Ret,
    Constant {
        operand_type: Type,
        constant: LiteralValue,
    },
    Unary {
        operand_type: Type,
        operator: UnaryOperator,
        operand: &'a Instruction<'a>,
    },
    Binary {
        operand_type: Type,
        operator: BinaryOperator,
        left: &'a Instruction<'a>,
        right: &'a Instruction<'a>,
    },
}

#[derive(Debug, PartialEq)]
pub struct Instruction<'a> {
    pub name: &'a str,
    pub payload: InstructionPayload<'a>,
}

impl InstructionPayload<'_> {
    pub fn instruction_type(&self) -> Option<Type> {
        match self {
            InstructionPayload::Ret => None,
            InstructionPayload::Constant { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload::Unary { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload::Binary { operand_type, .. } => Some(operand_type.clone()),
        }
    }
}

impl<'a> Instruction<'a> {
    pub fn instruction_type(&self) -> Option<Type> {
        self.payload.instruction_type()
    }

    fn new_const<'n>(name: &'n str, constant: LiteralValue) -> Self
    where
        'n: 'a,
    {
        Self {
            name,
            payload: InstructionPayload::Constant {
                operand_type: Type::of_literal(&constant),
                constant,
            },
        }
    }

    fn new_ret<'n>(name: &'n str) -> Self
    where
        'n: 'a,
    {
        Self {
            name,
            payload: InstructionPayload::Ret {},
        }
    }

    fn new_unary<'n>(
        name: &'n str,
        operand_type: Type,
        operator: UnaryOperator,
        operand: &'n Instruction<'n>,
    ) -> Self
    where
        'n: 'a,
    {
        Self {
            name,
            payload: InstructionPayload::Unary {
                operand_type,
                operator,
                operand,
            },
        }
    }

    fn new_binary<'n>(
        name: &'n str,
        operand_type: Type,
        operator: BinaryOperator,
        left: &'n Instruction<'n>,
        right: &'n Instruction<'n>,
    ) -> Self
    where
        'n: 'a,
    {
        Self {
            name,
            payload: InstructionPayload::Binary {
                operand_type,
                operator,
                left,
                right,
            },
        }
    }
}

impl Display for InstructionPayload<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionPayload::Ret => write!(f, "ret()"),
            InstructionPayload::Constant {
                operand_type,
                constant,
            } => write!(
                f,
                "{} = const({})",
                operand_type.to_string_short(),
                constant
            ),
            InstructionPayload::Unary {
                operand_type,
                operator,
                operand,
            } => write!(
                f,
                "{} = {}({})",
                operand_type.to_string_short(),
                operator.name(),
                operand.name
            ),
            InstructionPayload::Binary {
                operand_type,
                operator,
                left,
                right,
            } => write!(
                f,
                "{} = {}({}, {})",
                operand_type.to_string_short(),
                operator.name(),
                left.name,
                right.name
            ),
        }
    }
}

impl Display for Instruction<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:-15} {}", self.name, self.payload)
    }
}

pub struct BasicBlock<'a> {
    // TODO: name
    pub instructions: RefCell<BumpVec<'a, &'a Instruction<'a>>>,
}

impl<'a> BasicBlock<'a> {
    pub fn new_in(ir: &'a Ir) -> Self {
        Self {
            instructions: RefCell::new(BumpVec::new_in(&ir.arena)),
        }
    }
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

impl Default for Ir {
    fn default() -> Self {
        Self::new()
    }
}

impl Ir {
    pub fn new() -> Self {
        Self {
            arena: bumpalo::Bump::new(),
        }
    }

    pub fn new_const(&self, name: &str, constant: LiteralValue) -> &Instruction {
        self.arena
            .alloc(Instruction::new_const(self.arena.alloc_str(name), constant))
    }

    pub fn new_ret(&self, name: &str) -> &Instruction {
        self.arena
            .alloc(Instruction::new_ret(self.arena.alloc_str(name)))
    }

    pub fn new_unary<'s>(
        &'s self,
        name: &str,
        operator: UnaryOperator,
        operand: &'s Instruction,
    ) -> &'s Instruction<'s> {
        self.arena.alloc(Instruction::new_unary(
            self.arena.alloc_str(name),
            operand
                .instruction_type()
                .expect("cannot have an unary instruction with a void operand"),
            operator,
            operand,
        ))
    }

    pub fn new_binary<'s>(
        &'s self,
        name: &str,
        operator: BinaryOperator,
        left: &'s Instruction,
        right: &'s Instruction,
    ) -> &'s Instruction<'s> {
        let left_type = left
            .instruction_type()
            .expect("cannot have a binary instruction with a void operand");
        assert_eq!(Some(left_type.clone()), right.instruction_type());

        self.arena.alloc(Instruction::new_binary(
            self.arena.alloc_str(name),
            left.instruction_type()
                .expect("cannot have a binary instruction with a void operand"),
            operator,
            left,
            right,
        ))
    }

    pub fn basic_block(&self) -> &BasicBlock {
        self.arena.alloc(BasicBlock {
            instructions: RefCell::new(BumpVec::new_in(&self.arena)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::UnaryOperator;

    #[test]
    fn test_display_instruction_no_args_no_const() {
        let ir = Ir::new();
        assert_eq!("ret_0           ret()", ir.new_ret("ret_0").to_string())
    }

    #[test]
    fn test_display_instruction_no_args_const() {
        let ir = Ir::new();
        assert_eq!(
            "const_0         i = const(1i)",
            ir.new_const("const_0", LiteralValue::Integer(1))
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_arg_no_const() {
        let ir = Ir::new();
        let const_0 = ir.new_const("const_0", LiteralValue::Integer(1));
        assert_eq!(
            "neg_0           i = neg(const_0)",
            ir.new_unary("neg_0", UnaryOperator::Neg, const_0)
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_args_no_const() {
        let ir = Ir::new();
        let const_0 = ir.new_const("const_0", LiteralValue::Integer(0));
        let const_1 = ir.new_const("const_1", LiteralValue::Integer(1));
        assert_eq!(
            "add_0           i = add(const_0, const_1)",
            ir.new_binary("add_0", BinaryOperator::Add, const_0, const_1)
                .to_string()
        )
    }
}
