use crate::{CodegenError, CodegenResult};
use kigiri_memory::{BumpArena, BumpVec, StringId, resolve_string_id};
use parser::{BinaryOperator, BlockId, LiteralValue, UnaryOperator};
use semantic_analysis::{ArgumentIndex, Type, VariableIndex};
use std::cell::RefCell;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
pub struct Module<'a> {
    pub name: StringId,
    pub functions: BumpVec<'a, &'a Function<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct Function<'a> {
    pub signature: &'a FunctionSignature<'a>,
    pub basic_blocks: BumpVec<'a, &'a BasicBlock<'a>>,
    pub entry_block_id: BlockId,
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Variable {
    pub index: VariableIndex,
    pub name: StringId,
    pub variable_type: Type,
}

#[derive(Debug, PartialEq)]
pub struct BasicBlock<'a> {
    pub id: BlockId,
    pub instructions: RefCell<BumpVec<'a, &'a Instruction>>,
    pub variables: RefCell<BumpVec<'a, Variable>>,
}

#[derive(Debug, PartialEq)]
pub struct Instruction {
    pub id: InstructionId,
    pub payload: InstructionPayload,
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
        result_type: Type,
        operator: UnaryOperator,
        operand: InstructionId,
    },
    Binary {
        result_type: Type,
        operator: BinaryOperator,
        operand_type: Type,
        left: InstructionId,
        right: InstructionId,
    },
    LoadVar {
        name: StringId,
        operand_type: Type,
        variable_index: VariableIndex,
    },
    LoadArg {
        name: StringId,
        operand_type: Type,
        argument_index: ArgumentIndex,
    },
    StoreVar {
        name: StringId,
        operand_type: Type,
        variable_index: VariableIndex,
        value: InstructionId,
    },
    Let {
        name: StringId,
        operand_type: Type,
        variable_index: VariableIndex,
        initializer: InstructionId,
    },
    Call {
        function_name: StringId,
        return_type: Option<Type>,
        arguments: Vec<InstructionId>,
    },
    Jump {
        target_block: BlockId,
    },
    Branch {
        condition: InstructionId,
        then_block: BlockId,
        else_block: BlockId,
    },
}

// Impls

impl InstructionId {
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl InstructionPayload {
    pub fn instruction_type(&self) -> Option<Type> {
        match self {
            InstructionPayload::RetExpr { operand_type, .. } => Some(*operand_type),
            InstructionPayload::Ret => None,
            InstructionPayload::Constant { operand_type, .. } => Some(*operand_type),
            InstructionPayload::Unary { result_type, .. } => Some(*result_type),
            InstructionPayload::Binary { result_type, .. } => Some(*result_type),
            InstructionPayload::LoadVar { operand_type, .. } => Some(*operand_type),
            InstructionPayload::LoadArg { operand_type, .. } => Some(*operand_type),
            InstructionPayload::StoreVar { operand_type, .. } => Some(*operand_type),
            InstructionPayload::Let { operand_type, .. } => Some(*operand_type),
            InstructionPayload::Call { return_type, .. } => *return_type,
            InstructionPayload::Jump { .. } => None,
            InstructionPayload::Branch { .. } => None,
        }
    }
}

impl Instruction {
    pub fn instruction_type(&self) -> Option<Type> {
        self.payload.instruction_type()
    }
}

// Display impls

impl Display for Module<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "module {}",
            resolve_string_id(self.name).ok_or(std::fmt::Error)?
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
            resolve_string_id(self.signature.name).ok_or(std::fmt::Error)?
        )?;
        for arg in self.signature.arguments.iter() {
            writeln!(
                f,
                "  {}: {},",
                resolve_string_id(arg.name).ok_or(std::fmt::Error)?,
                arg.argument_type,
            )?;
        }
        writeln!(
            f,
            ") -> {} {{",
            self.signature
                .return_type
                .as_ref()
                .map_or("void", |t| t.to_string_short())
        )?;
        writeln!(f, "  entry_block: #{}", self.entry_block_id.0)?;
        for block in &self.basic_blocks {
            for line in format!("{}", block).lines() {
                writeln!(f, "  {}", line)?;
            }
        }
        write!(f, "}}")
    }
}

impl Display for BasicBlock<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{ #{}", self.id.0)?;

        let variables = self.variables.borrow();
        for var in variables.iter() {
            writeln!(
                f,
                "  var {}: {}",
                resolve_string_id(var.name).ok_or(std::fmt::Error)?,
                var.variable_type
            )?;
        }

        let instructions = self.instructions.borrow();
        for instr in instructions.iter() {
            writeln!(f, "  {}", instr)?;
        }
        write!(f, "}}")
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:05} {:3} {}",
            self.id.0,
            self.payload
                .instruction_type()
                .map(|t| t.to_string_short())
                .unwrap_or("v"),
            self.payload
        )
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
            InstructionPayload::RetExpr { expression, .. } => write!(f, "ret @{}", expression),
            InstructionPayload::Ret => write!(f, "ret"),
            InstructionPayload::Constant { constant, .. } => write!(f, "const {}", constant),
            InstructionPayload::Unary {
                operator, operand, ..
            } => write!(f, "{} @{}", operator.name(), operand),
            InstructionPayload::Binary {
                operator,
                left,
                right,
                ..
            } => write!(f, "{} @{}, @{}", operator.name(), left, right),
            InstructionPayload::LoadVar { name, .. } => {
                write!(
                    f,
                    "loadvar {}",
                    resolve_string_id(*name).ok_or(std::fmt::Error)?
                )
            }
            InstructionPayload::LoadArg { name, .. } => {
                write!(
                    f,
                    "loadarg {}",
                    resolve_string_id(*name).ok_or(std::fmt::Error)?
                )
            }
            InstructionPayload::StoreVar { name, value, .. } => {
                write!(
                    f,
                    "storevar {} = @{}",
                    resolve_string_id(*name).ok_or(std::fmt::Error)?,
                    value
                )
            }
            InstructionPayload::Let {
                name, initializer, ..
            } => {
                write!(
                    f,
                    "let {} = @{}",
                    resolve_string_id(*name).ok_or(std::fmt::Error)?,
                    initializer
                )
            }
            InstructionPayload::Call {
                function_name,
                arguments,
                ..
            } => {
                write!(
                    f,
                    "call {}(",
                    resolve_string_id(*function_name).ok_or(std::fmt::Error)?
                )?;
                for (i, arg) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "@{}", arg)?;
                }
                write!(f, ")")
            }
            InstructionPayload::Jump { target_block } => write!(f, "jmp #{}", target_block.0),
            InstructionPayload::Branch {
                condition,
                then_block,
                else_block,
            } => {
                write!(f, "br @{}, #{}, #{}", condition, then_block.0, else_block.0)
            }
        }
    }
}

// IR allocator

pub struct IrAllocator {
    arena: BumpArena,
    next_basic_block_id: RefCell<u32>,
    next_instruction_id: RefCell<u32>,
}

impl Default for IrAllocator {
    fn default() -> Self {
        Self::new()
    }
}

impl IrAllocator {
    pub fn new() -> Self {
        Self {
            arena: BumpArena::new(),
            next_basic_block_id: RefCell::new(0u32),
            next_instruction_id: RefCell::new(0u32),
        }
    }

    fn next_basic_block_id(&self) -> BlockId {
        let old = self.next_basic_block_id.replace_with(|u| *u + 1);
        BlockId(old)
    }

    pub fn reset_block_id(&self) {
        self.next_basic_block_id.replace(0);
    }

    fn next_instruction_id(&self) -> InstructionId {
        let old = self.next_instruction_id.replace_with(|u| *u + 1);
        InstructionId(old)
    }

    pub fn reset_instruction_id(&self) {
        self.next_instruction_id.replace(0);
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

    pub fn new_ret_expr(&self, expression: &Instruction) -> CodegenResult<&Instruction> {
        let operand_type =
            expression
                .instruction_type()
                .ok_or_else(|| CodegenError::InternalError {
                    message: "cannot have a ret expression with a void operand".to_string(),
                })?;
        Ok(self.new_instruction(InstructionPayload::RetExpr {
            operand_type,
            expression: expression.id,
        }))
    }

    pub fn new_unary<'s>(
        &'s self,
        operator: UnaryOperator,
        operand: &'s Instruction,
    ) -> CodegenResult<&'s Instruction> {
        let operand_type =
            operand
                .instruction_type()
                .ok_or_else(|| CodegenError::InternalError {
                    message: "cannot have a unary expression with a void operand".to_string(),
                })?;
        Ok(self.new_instruction(InstructionPayload::Unary {
            result_type: operand_type,
            operator,
            operand: operand.id,
        }))
    }

    pub fn new_binary<'s>(
        &'s self,
        operator: BinaryOperator,
        result_type: &Type,
        operand_type: &Type,
        left: &'s Instruction,
        right: &'s Instruction,
    ) -> CodegenResult<&'s Instruction> {
        let left_type = left
            .instruction_type()
            .ok_or_else(|| CodegenError::InternalError {
                message: "cannot have a binary instruction with a void left operand".to_string(),
            })?;
        let right_type = right
            .instruction_type()
            .ok_or_else(|| CodegenError::InternalError {
                message: "cannot have a binary instruction with a void right operand".to_string(),
            })?;

        if left_type != right_type {
            return Err(CodegenError::InternalError {
                message: format!(
                    "binary operand type mismatch: left {:?}, right {:?}",
                    left_type, right_type
                ),
            });
        }

        Ok(self.new_instruction(InstructionPayload::Binary {
            result_type: *result_type,
            operator,
            operand_type: *operand_type,
            left: left.id,
            right: right.id,
        }))
    }

    pub fn new_load_var(
        &self,
        name: StringId,
        operand_type: Type,
        index: VariableIndex,
    ) -> &Instruction {
        self.new_instruction(InstructionPayload::LoadVar {
            name,
            operand_type,
            variable_index: index,
        })
    }

    pub fn new_load_arg(
        &self,
        name: StringId,
        operand_type: Type,
        index: ArgumentIndex,
    ) -> &Instruction {
        self.new_instruction(InstructionPayload::LoadArg {
            name,
            operand_type,
            argument_index: index,
        })
    }

    pub fn new_let(
        &self,
        variable_index: VariableIndex,
        name: StringId,
        operand_type: Type,
        initializer: InstructionId,
    ) -> &Instruction {
        self.new_instruction(InstructionPayload::Let {
            variable_index,
            name,
            operand_type,
            initializer,
        })
    }

    pub fn new_store(
        &self,
        name: StringId,
        operand_type: Type,
        variable_index: VariableIndex,
        value: &Instruction,
    ) -> &Instruction {
        self.new_instruction(InstructionPayload::StoreVar {
            name,
            operand_type,
            variable_index,
            value: value.id,
        })
    }

    pub fn new_call(
        &self,
        function_name: StringId,
        return_type: Option<Type>,
        arguments: Vec<&Instruction>,
    ) -> &Instruction {
        let argument_ids = arguments.iter().map(|arg| arg.id).collect();
        self.new_instruction(InstructionPayload::Call {
            function_name,
            return_type,
            arguments: argument_ids,
        })
    }

    pub fn basic_block(&self) -> &BasicBlock {
        self.arena.alloc(BasicBlock {
            id: self.next_basic_block_id(),
            instructions: RefCell::new(BumpVec::new_in(&self.arena)),
            variables: RefCell::new(BumpVec::new_in(&self.arena)),
        })
    }

    pub fn functions(&self) -> BumpVec<&Function> {
        BumpVec::new_in(&self.arena)
    }

    pub fn basic_blocks(&self) -> BumpVec<&BasicBlock> {
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

    pub fn new_jump(&self, target_block: BlockId) -> &Instruction {
        self.new_instruction(InstructionPayload::Jump { target_block })
    }

    pub fn new_branch(
        &self,
        condition: &Instruction,
        then_block: BlockId,
        else_block: BlockId,
    ) -> &Instruction {
        self.new_instruction(InstructionPayload::Branch {
            condition: condition.id,
            then_block,
            else_block,
        })
    }

    pub fn function<'s>(
        &'s self,
        signature: &'s FunctionSignature<'s>,
        basic_blocks: BumpVec<'s, &'s BasicBlock<'s>>,
        entry_block_id: BlockId,
    ) -> &'s Function<'s> {
        self.arena.alloc(Function {
            signature,
            basic_blocks,
            entry_block_id,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kigiri_memory::intern_string;
    use parser::UnaryOperator;

    #[test]
    fn test_display_instruction_ret() {
        let ir_allocator = IrAllocator::new();
        assert_eq!("00000 v   ret", ir_allocator.new_ret().to_string())
    }

    #[test]
    fn test_display_instruction_ret_expr() {
        let ir_allocator = IrAllocator::new();
        let const_0 = ir_allocator.new_const(LiteralValue::I16(1));
        assert_eq!(
            "00001 i16 ret @0",
            ir_allocator
                .new_ret_expr(const_0)
                .expect("should succeed")
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_const() {
        let ir_allocator = IrAllocator::new();
        assert_eq!(
            "00000 i64 const 1i64",
            ir_allocator.new_const(LiteralValue::I64(1)).to_string()
        )
    }

    #[test]
    fn test_display_instruction_unary() {
        let ir_allocator = IrAllocator::new();
        let const_0 = ir_allocator.new_const(LiteralValue::I8(1));
        assert_eq!(
            "00001 i8  neg @0",
            ir_allocator
                .new_unary(UnaryOperator::Neg, const_0)
                .expect("should succeed")
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_binary() {
        let ir_allocator = IrAllocator::new();
        let const_0 = ir_allocator.new_const(LiteralValue::I32(0));
        let const_1 = ir_allocator.new_const(LiteralValue::I32(1));
        assert_eq!(
            "00002 i32 add @0, @1",
            ir_allocator
                .new_binary(
                    BinaryOperator::Add,
                    &Type::I32,
                    &Type::I32,
                    const_0,
                    const_1
                )
                .expect("should succeed")
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_call() {
        let ir_allocator = IrAllocator::new();
        let const_0 = ir_allocator.new_const(LiteralValue::I32(42));
        let const_1 = ir_allocator.new_const(LiteralValue::I32(10));
        let function_name = intern_string("test_func");
        assert_eq!(
            "00002 i32 call test_func(@0, @1)",
            ir_allocator
                .new_call(function_name, Some(Type::I32), vec![const_0, const_1])
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_call_void() {
        let ir_allocator = IrAllocator::new();
        let const_0 = ir_allocator.new_const(LiteralValue::I32(42));
        let function_name = intern_string("print");
        assert_eq!(
            "00001 v   call print(@0)",
            ir_allocator
                .new_call(function_name, None, vec![const_0])
                .to_string()
        )
    }

    #[test]
    fn test_display_instruction_jump() {
        let ir_allocator = IrAllocator::new();
        let target_block = BlockId(5);
        assert_eq!(
            "00000 v   jmp #5",
            ir_allocator.new_jump(target_block).to_string()
        )
    }

    #[test]
    fn test_display_instruction_branch() {
        let ir_allocator = IrAllocator::new();
        let condition = ir_allocator.new_const(LiteralValue::Boolean(true));
        let then_block = BlockId(1);
        let else_block = BlockId(2);
        assert_eq!(
            "00001 v   br @0, #1, #2",
            ir_allocator
                .new_branch(condition, then_block, else_block)
                .to_string()
        )
    }
}
