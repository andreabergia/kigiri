use bumpalo::collections::Vec as BumpVec;
use parser::{BinaryOperator, LiteralValue, UnaryOperator};
use std::cell::RefCell;
use std::fmt::{Binary, Display, Formatter};
use type_engine::Type;

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

#[derive(Debug, Clone, PartialEq)]
pub struct Instruction<'a> {
    pub operand_type: Option<Type>,
    pub name: &'a str,
    pub instruction_type: InstructionType,
    pub args: BumpVec<'a, &'a Instruction<'a>>,
    pub constant: Option<LiteralValue>,
}

impl<'a> Instruction<'a> {
    fn new_const<'n>(arena: &'a bumpalo::Bump, name: &'n str, constant: LiteralValue) -> Self
    where
        'n: 'a,
    {
        Self {
            operand_type: Some(Type::of_literal(&constant)),
            name,
            instruction_type: InstructionType::Const,
            args: BumpVec::new_in(arena),
            constant: Some(constant),
        }
    }

    fn new_ret<'n>(arena: &'a bumpalo::Bump, name: &'n str) -> Self
    where
        'n: 'a,
    {
        Self {
            operand_type: None,
            name,
            instruction_type: InstructionType::Ret,
            args: BumpVec::new_in(arena),
            constant: None,
        }
    }
}

impl Display for Instruction<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {:-12} = {}(",
            match &self.operand_type {
                None => "v".to_string(),
                Some(operand_type) => operand_type.to_string_short(),
            },
            self.name,
            self.instruction_type,
        )?;
        let mut needs_comma = false;
        for arg in self.args.iter() {
            if needs_comma {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg.name)?;
            needs_comma = true;
        }
        if let Some(constant) = &self.constant {
            if needs_comma {
                write!(f, ", ")?;
            }
            write!(f, "{}", constant)?;
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

    fn instruction<'s>(
        &'s self,
        operand_type: Option<Type>,
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

    pub fn new_const(&self, name: &str, constant: LiteralValue) -> &Instruction {
        self.instruction(
            Some(Type::of_literal(&constant)),
            name,
            InstructionType::Const,
            [],
            Some(constant),
        )
    }

    pub fn new_ret(&self, name: &str) -> &Instruction {
        self.instruction(None, name, InstructionType::Ret, [], None)
    }

    pub fn new_unary<'s>(
        &'s self,
        name: &str,
        operator: UnaryOperator,
        instr: &'s Instruction,
    ) -> &'s Instruction<'s> {
        self.instruction(
            instr.operand_type.clone(),
            name,
            match operator {
                UnaryOperator::Neg => InstructionType::Neg,
                UnaryOperator::Not => InstructionType::Not,
                UnaryOperator::BitwiseNot => InstructionType::BitwiseNot,
            },
            [instr],
            None,
        )
    }

    pub fn new_binary<'s>(
        &'s self,
        name: &str,
        operator: BinaryOperator,
        left: &'s Instruction,
        right: &'s Instruction,
    ) -> &'s Instruction<'s> {
        assert_eq!(left.operand_type, right.operand_type);

        self.instruction(
            left.operand_type.clone(),
            name,
            match operator {
                BinaryOperator::Add => InstructionType::Add,
                BinaryOperator::Sub => InstructionType::Sub,
                BinaryOperator::Mul => InstructionType::Mul,
                BinaryOperator::Div => InstructionType::Div,
                BinaryOperator::Rem => InstructionType::Rem,
                BinaryOperator::Exp => InstructionType::Exp,
                BinaryOperator::Eq => InstructionType::Eq,
                BinaryOperator::Neq => InstructionType::Neq,
                BinaryOperator::Lt => InstructionType::Lt,
                BinaryOperator::Lte => InstructionType::Lte,
                BinaryOperator::Gt => InstructionType::Gt,
                BinaryOperator::Gte => InstructionType::Gte,
                BinaryOperator::And => InstructionType::And,
                BinaryOperator::Or => InstructionType::Or,
                BinaryOperator::BitwiseAnd => InstructionType::BitwiseAnd,
                BinaryOperator::BitwiseOr => InstructionType::BitwiseOr,
                BinaryOperator::BitwiseXor => InstructionType::BitwiseXor,
                BinaryOperator::BitwiseShl => InstructionType::BitwiseShl,
                BinaryOperator::BitwiseShr => InstructionType::BitwiseShr,
            },
            [left, right],
            None,
        )
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
        assert_eq!("v ret_0        = ret()", ir.new_ret("ret_0").to_string())
    }

    #[test]
    fn test_display_instruction_no_args_const() {
        let ir = Ir::new();
        assert_eq!(
            "i const_0      = const(1i)",
            ir.new_const("const_0", LiteralValue::Integer(1))
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_arg_no_const() {
        let ir = Ir::new();
        let const_0 = ir.new_const("const_0", LiteralValue::Integer(1));
        assert_eq!(
            "i neg_0        = neg(const_0)",
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
            "i add_0        = add(const_0, const_1)",
            ir.new_binary("add_0", BinaryOperator::Add, const_0, const_1)
                .to_string()
        )
    }
}
