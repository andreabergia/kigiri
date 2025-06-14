use bumpalo::collections::Vec as BumpVec;
use parser::{BinaryOperator, BlockId, LiteralValue, StringId, UnaryOperator, resolve_string_id};
use semantic_analysis::{SymbolId, Type};
use std::any::Any;
use std::cell::RefCell;
use std::fmt::{Binary, Display, Formatter};

#[derive(Debug, PartialEq)]
pub struct Module<'a> {
    pub name: StringId,
    pub functions: BumpVec<'a, &'a Function<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct Function<'a> {
    pub signature: &'a FunctionSignature<'a>,
    pub body: &'a BasicBlock<'a>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionSignature<'a> {
    pub name: StringId,
    pub return_type: Option<Type>,
    pub arguments: BumpVec<'a, FunctionArgument>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionArgument {
    pub name: StringId,
    pub argument_type: Type,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: StringId,
    pub symbol_type: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstructionId(u32);

#[derive(Debug, PartialEq)]
pub enum InstructionPayload {
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
pub struct Instruction {
    pub id: InstructionId,
    pub payload: InstructionPayload,
}

impl InstructionId {
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl InstructionPayload {
    pub fn instruction_type(&self) -> Option<Type> {
        match self {
            InstructionPayload::RetExpr { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload::Ret => None,
            InstructionPayload::Constant { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload::Unary { operand_type, .. } => Some(operand_type.clone()),
            InstructionPayload::Binary { operand_type, .. } => Some(operand_type.clone()),
        }
    }
}

impl Instruction {
    pub fn instruction_type(&self) -> Option<Type> {
        self.payload.instruction_type()
    }
}

impl Display for InstructionId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for InstructionPayload {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionPayload::RetExpr {
                operand_type,
                expression,
            } => write!(f, "ret @{}", expression),
            InstructionPayload::Ret => write!(f, "ret"),
            InstructionPayload::Constant {
                operand_type,
                constant,
            } => write!(f, "const {}", constant),
            InstructionPayload::Unary {
                operand_type,
                operator,
                operand,
            } => write!(f, "{} @{}", operator.name(), operand),
            InstructionPayload::Binary {
                operand_type,
                operator,
                left,
                right,
            } => write!(f, "{} @{}, @{}", operator.name(), left, right),
        }
    }
}

impl Display for Instruction {
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

#[derive(Debug, PartialEq)]
pub struct BasicBlock<'a> {
    pub id: BlockId,
    pub instructions: RefCell<BumpVec<'a, &'a Instruction>>,
}

impl Display for BasicBlock<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{ #{}", self.id.0)?;
        let instructions = self.instructions.borrow();
        for instr in instructions.iter() {
            writeln!(f, "  {}", instr)?;
        }
        write!(f, "}}")
    }
}

pub struct Ir {
    arena: bumpalo::Bump,
    next_basic_block_id: RefCell<u32>,
    next_instruction_id: RefCell<u32>,
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
            next_basic_block_id: RefCell::new(0u32),
            next_instruction_id: RefCell::new(0u32),
        }
    }

    fn next_basic_block_id(&self) -> BlockId {
        let old = self.next_basic_block_id.replace_with(|u| *u + 1);
        BlockId(old)
    }

    fn next_instruction_id(&self) -> InstructionId {
        let old = self.next_instruction_id.replace_with(|u| *u + 1);
        InstructionId(old)
    }

    fn new_instruction(&self, payload: InstructionPayload) -> &Instruction {
        self.arena.alloc(Instruction {
            id: self.next_instruction_id(),
            payload,
        })
    }

    pub fn new_const(&self, constant: LiteralValue) -> &Instruction {
        self.new_instruction(InstructionPayload::Constant {
            operand_type: Type::of_literal(&constant),
            constant,
        })
    }

    pub fn new_ret(&self) -> &Instruction {
        self.new_instruction(InstructionPayload::Ret)
    }

    pub fn new_ret_expr<'s>(&'s self, expression: &Instruction) -> &'s Instruction {
        let operand_type = expression
            .instruction_type()
            .expect("cannot have a ret expression with a void operand");
        self.new_instruction(InstructionPayload::RetExpr {
            operand_type,
            expression: expression.id,
        })
    }

    pub fn new_unary<'s>(
        &'s self,
        operator: UnaryOperator,
        operand: &'s Instruction,
    ) -> &'s Instruction {
        let operand_type = operand
            .instruction_type()
            .expect("cannot have an unary expression with a void operand");
        self.new_instruction(InstructionPayload::Unary {
            operand_type,
            operator,
            operand: operand.id,
        })
    }

    pub fn new_binary<'s>(
        &'s self,
        operator: BinaryOperator,
        left: &'s Instruction,
        right: &'s Instruction,
    ) -> &'s Instruction {
        let left_type = left
            .instruction_type()
            .expect("cannot have a binary instruction with a void operand");
        assert_eq!(Some(left_type.clone()), right.instruction_type());

        self.new_instruction(InstructionPayload::Binary {
            operand_type: left_type,
            operator,
            left: left.id,
            right: right.id,
        })
    }

    pub fn basic_block(&self) -> &BasicBlock {
        self.arena.alloc(BasicBlock {
            id: self.next_basic_block_id(),
            instructions: RefCell::new(BumpVec::new_in(&self.arena)),
        })
    }

    pub fn functions(&self) -> BumpVec<&Function> {
        BumpVec::new_in(&self.arena)
    }

    pub fn module<'s>(
        &'s self,
        name: StringId,
        functions: BumpVec<'s, &'s Function<'s>>,
    ) -> &'s Module<'s> {
        self.arena.alloc(Module { name, functions })
    }

    pub fn function_arguments(
        &self,
        iter: impl IntoIterator<Item = FunctionArgument>,
    ) -> BumpVec<FunctionArgument> {
        BumpVec::from_iter_in(iter, &self.arena)
    }

    pub fn function_signature<'s>(
        &'s self,
        name: StringId,
        return_type: Option<Type>,
        arguments: BumpVec<'s, FunctionArgument>,
    ) -> &'s FunctionSignature<'s> {
        self.arena.alloc(FunctionSignature {
            name,
            return_type,
            arguments,
        })
    }

    pub fn function<'s>(
        &'s self,
        signature: &'s FunctionSignature<'s>,
        body: &'s BasicBlock<'s>,
    ) -> &'s Function<'s> {
        self.arena.alloc(Function { signature, body })
    }
}

impl Display for Module<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "module {}",
            resolve_string_id(self.name).expect("should find module name")
        )?;
        writeln!(f)?;
        for function in &self.functions {
            writeln!(f, "{}", function)?;
        }
        Ok(())
    }
}

impl Display for Function<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "fn {}(",
            resolve_string_id(self.signature.name).expect("function name")
        )?;
        for arg in self.signature.arguments.iter() {
            writeln!(
                f,
                "  {}: {},",
                resolve_string_id(arg.name).expect("argument name"),
                arg.argument_type.to_string_short(),
            )?;
        }
        writeln!(
            f,
            ") -> {}",
            self.signature
                .return_type
                .as_ref()
                .map_or("void".to_string(), |t| t.to_string_short())
        )?;
        write!(f, "{}", self.body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::UnaryOperator;

    #[test]
    fn test_display_instruction_ret() {
        let ir = Ir::new();
        assert_eq!("00000 v ret", ir.new_ret().to_string())
    }

    #[test]
    fn test_display_instruction_ret_expr() {
        let ir = Ir::new();
        let const_0 = ir.new_const(LiteralValue::Integer(1));
        assert_eq!("00001 i ret @0", ir.new_ret_expr(const_0).to_string())
    }

    #[test]
    fn test_display_instruction_const() {
        let ir = Ir::new();
        assert_eq!(
            "00000 i const 1i",
            ir.new_const(LiteralValue::Integer(1)).to_string()
        )
    }

    #[test]
    fn test_display_instruction_unary() {
        let ir = Ir::new();
        let const_0 = ir.new_const(LiteralValue::Integer(1));
        assert_eq!(
            "00001 i neg @0",
            ir.new_unary(UnaryOperator::Neg, const_0).to_string()
        )
    }

    #[test]
    fn test_display_instruction_binary() {
        let ir = Ir::new();
        let const_0 = ir.new_const(LiteralValue::Integer(0));
        let const_1 = ir.new_const(LiteralValue::Integer(1));
        assert_eq!(
            "00002 i add @0, @1",
            ir.new_binary(BinaryOperator::Add, const_0, const_1)
                .to_string()
        )
    }
}
