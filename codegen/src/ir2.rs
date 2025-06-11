use bumpalo::collections::Vec as BumpVec;
use parser::{BinaryOperator, LiteralValue, UnaryOperator};
use semantic_analysis::Type;
use std::any::Any;
use std::cell::RefCell;
use std::fmt::{Binary, Display, Formatter};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstructionId(pub u32);

#[derive(Debug, PartialEq)]
pub enum InstructionPayload2 {
    RetExpr {
        operand_type: Type,
        expression: InstructionId,
    },
    Ret,
    Constant {
        operand_type: Type,
        constant: LiteralValue,
    },
    Unary {
        operand_type: Type,
        operator: UnaryOperator,
        operand: InstructionId,
    },
    Binary {
        operand_type: Type,
        operator: BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    },
}

#[derive(Debug, PartialEq)]
pub struct Instruction2 {
    pub id: InstructionId,
    pub payload: InstructionPayload2,
}

impl InstructionPayload2 {
    pub fn instruction_type(&self) -> Option<Type> {
        match self {
            InstructionPayload2::RetExpr { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload2::Ret => None,
            InstructionPayload2::Constant { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload2::Unary { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload2::Binary { operand_type, .. } => Some(operand_type.clone()),
        }
    }
}

impl Instruction2 {
    pub fn instruction_type(&self) -> Option<Type> {
        self.payload.instruction_type()
    }
}

impl Display for InstructionId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for InstructionPayload2 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionPayload2::RetExpr {
                operand_type,
                expression,
            } => write!(f, "ret @{}", expression),
            InstructionPayload2::Ret => write!(f, "ret"),
            InstructionPayload2::Constant {
                operand_type,
                constant,
            } => write!(f, "const {}", constant),
            InstructionPayload2::Unary {
                operand_type,
                operator,
                operand,
            } => write!(f, "{} @{}", operator.name(), operand),
            InstructionPayload2::Binary {
                operand_type,
                operator,
                left,
                right,
            } => write!(f, "{} @{}, @{}", operator.name(), left, right),
        }
    }
}

impl Display for Instruction2 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:05} {} {}",
            self.id.0,
            self.payload
                .instruction_type()
                .map(|t| t.to_string_short())
                .unwrap_or("v".to_string()),
            self.payload
        )
    }
}

pub struct BasicBlock2<'a> {
    // TODO: name
    pub instructions: RefCell<BumpVec<'a, &'a Instruction2>>,
}

impl<'a> BasicBlock2<'a> {
    pub fn new_in(ir: &'a Ir2) -> Self {
        Self {
            instructions: RefCell::new(BumpVec::new_in(&ir.arena)),
        }
    }
}

impl Display for BasicBlock2<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let instructions = self.instructions.borrow();
        for instr in instructions.iter() {
            writeln!(f, "{}", instr)?;
        }
        Ok(())
    }
}

pub struct Ir2 {
    arena: bumpalo::Bump,
    next_id_counter: RefCell<u32>,
}

impl Default for Ir2 {
    fn default() -> Self {
        Self::new()
    }
}

impl Ir2 {
    pub fn new() -> Self {
        Self {
            arena: bumpalo::Bump::new(),
            next_id_counter: RefCell::new(0u32),
        }
    }

    fn next_id(&self) -> InstructionId {
        let old = self.next_id_counter.replace_with(|u| *u + 1);
        InstructionId(old)
    }

    fn new_instruction(&self, payload: InstructionPayload2) -> &Instruction2 {
        self.arena.alloc(Instruction2 {
            id: self.next_id(),
            payload,
        })
    }

    pub fn new_const(&self, constant: LiteralValue) -> &Instruction2 {
        self.new_instruction(InstructionPayload2::Constant {
            operand_type: Type::of_literal(&constant),
            constant,
        })
    }

    pub fn new_ret(&self) -> &Instruction2 {
        self.new_instruction(InstructionPayload2::Ret)
    }

    pub fn new_ret_expr<'s>(&'s self, expression: &Instruction2) -> &'s Instruction2 {
        let operand_type = expression
            .instruction_type()
            .expect("cannot have a ret expression with a void operand");
        self.new_instruction(InstructionPayload2::RetExpr {
            operand_type,
            expression: expression.id,
        })
    }

    pub fn new_unary<'s>(
        &'s self,
        operator: UnaryOperator,
        operand: &'s Instruction2,
    ) -> &'s Instruction2 {
        let operand_type = operand
            .instruction_type()
            .expect("cannot have an unary expression with a void operand");
        self.new_instruction(InstructionPayload2::Unary {
            operand_type,
            operator,
            operand: operand.id,
        })
    }

    pub fn new_binary<'s>(
        &'s self,
        operator: BinaryOperator,
        left: &'s Instruction2,
        right: &'s Instruction2,
    ) -> &'s Instruction2 {
        let left_type = left
            .instruction_type()
            .expect("cannot have a binary instruction with a void operand");
        assert_eq!(Some(left_type.clone()), right.instruction_type());

        self.new_instruction(InstructionPayload2::Binary {
            operand_type: left_type,
            operator,
            left: left.id,
            right: right.id,
        })
    }

    pub fn basic_block(&self) -> &BasicBlock2 {
        self.arena.alloc(BasicBlock2 {
            instructions: RefCell::new(BumpVec::new_in(&self.arena)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::UnaryOperator;

    #[test]
    fn test_display_instruction_ret() {
        let ir = Ir2::new();
        assert_eq!("00000 v ret", ir.new_ret().to_string())
    }

    #[test]
    fn test_display_instruction_ret_expr() {
        let ir = Ir2::new();
        let const_0 = ir.new_const(LiteralValue::Integer(1));
        assert_eq!("00001 i ret @0", ir.new_ret_expr(const_0).to_string())
    }

    #[test]
    fn test_display_instruction_const() {
        let ir = Ir2::new();
        assert_eq!(
            "00000 i const 1i",
            ir.new_const(LiteralValue::Integer(1)).to_string()
        )
    }

    #[test]
    fn test_display_instruction_unary() {
        let ir = Ir2::new();
        let const_0 = ir.new_const(LiteralValue::Integer(1));
        assert_eq!(
            "00001 i neg @0",
            ir.new_unary(UnaryOperator::Neg, const_0).to_string()
        )
    }

    #[test]
    fn test_display_instruction_binary() {
        let ir = Ir2::new();
        let const_0 = ir.new_const(LiteralValue::Integer(0));
        let const_1 = ir.new_const(LiteralValue::Integer(1));
        assert_eq!(
            "00002 i add @0, @1",
            ir.new_binary(BinaryOperator::Add, const_0, const_1)
                .to_string()
        )
    }
}
