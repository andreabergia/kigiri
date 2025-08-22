use codegen::{Function, Instruction, InstructionId, InstructionPayload, LiteralValue};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, FloatType, FunctionType, IntType};
use inkwell::values::{
    BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue, PointerValue,
};
use inkwell::{FloatPredicate, IntPredicate};
use kigiri_memory::{StringId, resolve_string_id};
use parser::{BinaryOperator, BlockId, UnaryOperator};
use semantic_analysis::{ArgumentIndex, Type, VariableIndex};
use std::cell::RefCell;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
pub enum CodeGenError {
    #[error("LLVM builder error: {0}")]
    Builder(#[from] BuilderError),
    #[error("Internal error: {message}")]
    InternalError { message: String },
}

fn safe_resolve_string_id(id: StringId) -> Result<&'static str, CodeGenError> {
    resolve_string_id(id).ok_or_else(|| CodeGenError::InternalError {
        message: format!("Invalid string ID: {:?}", id),
    })
}

struct LlvmFunctionGenerator<'c, 'c2, 'ir, 'ir2> {
    context: &'c Context,
    builder: &'c2 Builder<'c>,
    function: &'ir Function<'ir2>,

    // Values are indexed by instruction id. There's a bit of space wasted because not all IR
    // expressions have a resulting value, but most do. And this everything quite simple and faster
    // than alternative approaches with hash maps.
    llvm_values: RefCell<Vec<Option<BasicValueEnum<'c>>>>,

    // Variables are indexed by their index
    variables: RefCell<Vec<PointerValue<'c>>>,

    // Maps block IDs to LLVM basic blocks
    llvm_blocks: RefCell<HashMap<BlockId, BasicBlock<'c>>>,
}

impl<'c, 'c2, 'ir, 'ir2> LlvmFunctionGenerator<'c, 'c2, 'ir, 'ir2> {
    fn new(context: &'c Context, builder: &'c2 Builder<'c>, function: &'ir Function<'ir2>) -> Self {
        // Calculate total instructions across all blocks to size the vector appropriately
        let total_instructions: usize = function
            .basic_blocks
            .iter()
            .map(|block| block.instructions.borrow().len())
            .sum();

        let mut llvm_values = Vec::with_capacity(total_instructions);
        llvm_values.resize(total_instructions, None);

        let total_variables: usize = function
            .basic_blocks
            .iter()
            .map(|block| block.variables.borrow().len())
            .sum();
        let variables = Vec::with_capacity(total_variables);

        Self {
            context,
            builder,
            function,
            llvm_values: llvm_values.into(),
            variables: variables.into(),
            llvm_blocks: RefCell::new(HashMap::new()),
        }
    }

    fn alloca_variables(&self) -> Result<(), CodeGenError> {
        // Sort cross-block variables by their index, to ensure correct allocation order
        let mut all_variables = Vec::new();
        for block in self.function.basic_blocks.iter() {
            for var in block.variables.borrow().iter() {
                all_variables.push(*var);
            }
        }
        all_variables.sort_by_key(|var| usize::from(var.index));

        // Allocate variables in index order
        for var in all_variables {
            let name = safe_resolve_string_id(var.name)?;
            let value = self.alloca_for_type(&var.variable_type, name)?;
            self.variables.borrow_mut().push(value);
        }
        Ok(())
    }

    fn store_value(&self, id: InstructionId, value: BasicValueEnum<'c>) {
        self.llvm_values.borrow_mut()[id.as_usize()] = Some(value);
    }

    fn get_int_value(&self, id: InstructionId) -> Result<IntValue<'c>, CodeGenError> {
        Ok(self.get_value(id)?.into_int_value())
    }

    fn get_bool_value(&self, id: InstructionId) -> Result<IntValue<'c>, CodeGenError> {
        Ok(self.get_value(id)?.into_int_value())
    }

    fn get_float_value(&self, id: InstructionId) -> Result<FloatValue<'c>, CodeGenError> {
        Ok(self.get_value(id)?.into_float_value())
    }

    fn get_value(&self, id: InstructionId) -> Result<BasicValueEnum<'c>, CodeGenError> {
        let values = self.llvm_values.borrow();
        let value = values
            .get(id.as_usize())
            .and_then(|opt| opt.as_ref())
            .ok_or_else(|| CodeGenError::InternalError {
                message: format!("Instruction ID {} has no associated value", id.as_usize()),
            })?;
        Ok(*value)
    }

    fn alloca_for_type(&self, type_: &Type, name: &str) -> Result<PointerValue<'c>, BuilderError> {
        if type_.is_integer() || *type_ == Type::Bool {
            self.builder.build_alloca(self.llvm_int_type(type_), name)
        } else {
            self.builder.build_alloca(self.llvm_float_type(type_), name)
        }
    }

    fn llvm_int_type(&self, type_: &Type) -> IntType<'c> {
        match type_ {
            Type::I8 => self.context.i8_type(),
            Type::I16 => self.context.i16_type(),
            Type::I32 => self.context.i32_type(),
            Type::I64 => self.context.i64_type(),
            Type::Bool => self.context.bool_type(),
            _ => panic!("cannot get llvm_int_type for {}", type_),
        }
    }

    fn llvm_float_type(&self, type_: &Type) -> FloatType<'c> {
        match type_ {
            Type::F32 => self.context.f32_type(),
            Type::F64 => self.context.f64_type(),
            _ => panic!("cannot get llvm_float_type for {}", type_),
        }
    }

    fn llvm_type(&self, type_: &Type) -> BasicMetadataTypeEnum<'c> {
        match type_ {
            Type::I8 => self.context.i8_type().into(),
            Type::I16 => self.context.i16_type().into(),
            Type::I32 => self.context.i32_type().into(),
            Type::I64 => self.context.i64_type().into(),
            Type::Bool => self.context.bool_type().into(),
            Type::F32 => self.context.f32_type().into(),
            Type::F64 => self.context.f64_type().into(),
        }
    }

    fn get_variable(&self, index: VariableIndex) -> Result<PointerValue<'c>, CodeGenError> {
        self.variables
            .borrow()
            .get(usize::from(index))
            .copied()
            .ok_or_else(|| CodeGenError::InternalError {
                message: format!("Variable index {} out of bounds", usize::from(index)),
            })
    }

    fn declare(&self, llvm_module: &Module<'c>) -> Result<FunctionValue<'c>, CodeGenError> {
        let fn_type = self.make_fun_type();
        let fun = llvm_module.add_function(
            safe_resolve_string_id(self.function.signature.name)?,
            fn_type,
            None,
        );

        self.setup_fun_arg(fun)?;
        Ok(fun)
    }

    fn generate_body(
        &self,
        fun: FunctionValue<'c>,
        llvm_module: &Module<'c>,
    ) -> Result<(), CodeGenError> {
        // Create LLVM basic blocks for non-empty IR basic blocks
        for ir_block in self.function.basic_blocks.iter() {
            if !ir_block.instructions.borrow().is_empty() {
                let block_name = &format!("bb{}", ir_block.id.0);
                let bb = self.context.append_basic_block(fun, block_name);
                self.llvm_blocks.borrow_mut().insert(ir_block.id, bb);
            }
        }

        // Position at entry block and allocate variables
        let entry_block_id = self.function.entry_block_id;
        let entry_bb = *self
            .llvm_blocks
            .borrow()
            .get(&entry_block_id)
            .ok_or_else(|| CodeGenError::InternalError {
                message: format!("Entry block {} not found", entry_block_id.0),
            })?;
        self.builder.position_at_end(entry_bb);
        self.alloca_variables()?;

        // Generate code for each non-empty basic block
        for ir_block in self.function.basic_blocks.iter() {
            if ir_block.instructions.borrow().is_empty() {
                continue;
            }

            let bb = *self.llvm_blocks.borrow().get(&ir_block.id).ok_or_else(|| {
                CodeGenError::InternalError {
                    message: format!("Basic block {} not found", ir_block.id.0),
                }
            })?;
            self.builder.position_at_end(bb);

            for instruction in ir_block.instructions.borrow().iter() {
                match &instruction.payload {
                    InstructionPayload::Constant { constant, .. } => {
                        self.handle_constant(instruction.id, constant);
                    }
                    InstructionPayload::Unary {
                        result_type: operand_type,
                        operator,
                        operand,
                    } => {
                        self.handle_unary(instruction.id, operand_type, operator, *operand)?;
                    }
                    InstructionPayload::Binary {
                        operator,
                        operand_type,
                        left,
                        right,
                        ..
                    } => {
                        self.handle_binary(instruction.id, operator, operand_type, *left, *right)?;
                    }
                    InstructionPayload::Ret => {
                        self.builder.build_return(None)?;
                    }
                    InstructionPayload::RetExpr {
                        expression,
                        operand_type,
                    } => {
                        self.handle_return_expression(*expression, operand_type)?;
                    }
                    InstructionPayload::LoadVar {
                        operand_type,
                        variable_index,
                        ..
                    } => {
                        self.handle_load_var(instruction, operand_type, *variable_index)?;
                    }
                    InstructionPayload::LoadArg { argument_index, .. } => {
                        self.handle_load_arg(fun, instruction, *argument_index)?;
                    }
                    InstructionPayload::StoreVar {
                        operand_type,
                        variable_index,
                        value,
                        ..
                    } => {
                        self.handle_store_var(operand_type, *variable_index, *value)?;
                    }
                    InstructionPayload::Let {
                        variable_index,
                        operand_type,
                        initializer,
                        ..
                    } => self.handle_let(*variable_index, operand_type, *initializer)?,
                    InstructionPayload::Call {
                        function_name,
                        return_type,
                        arguments,
                    } => {
                        self.handle_function_call(
                            instruction.id,
                            llvm_module,
                            function_name,
                            return_type,
                            arguments,
                        )?;
                    }
                    InstructionPayload::Jump { target_block } => {
                        self.handle_jump(*target_block)?;
                    }
                    InstructionPayload::Branch {
                        condition,
                        then_block,
                        else_block,
                    } => {
                        self.handle_branch(*condition, *then_block, *else_block)?;
                    }
                }
            }
        }

        if !fun.verify(true) {
            return Err(CodeGenError::InternalError {
                message: "LLVM function verification failed".to_string(),
            });
        }
        Ok(())
    }

    fn handle_load_var(
        &self,
        instruction: &Instruction,
        operand_type: &Type,
        variable_index: VariableIndex,
    ) -> Result<(), CodeGenError> {
        let var_pointer = self.get_variable(variable_index)?;

        let loaded_value = if operand_type.is_integer() || *operand_type == Type::Bool {
            self.builder.build_load(
                self.llvm_int_type(operand_type),
                var_pointer,
                &Self::name("load", instruction.id),
            )?
        } else {
            self.builder.build_load(
                self.llvm_float_type(operand_type),
                var_pointer,
                &Self::name("load", instruction.id),
            )?
        };
        self.store_value(instruction.id, loaded_value);
        Ok(())
    }

    fn handle_load_arg(
        &self,
        fun: FunctionValue<'c>,
        instruction: &Instruction,
        argument_index: ArgumentIndex,
    ) -> Result<(), CodeGenError> {
        let arg_idx: u32 = argument_index.into();
        let value = fun
            .get_nth_param(arg_idx)
            .ok_or_else(|| CodeGenError::InternalError {
                message: format!("Function argument {} not found", arg_idx),
            })?;
        self.store_value(instruction.id, value);
        Ok(())
    }

    fn handle_store_var(
        &self,
        operand_type: &Type,
        variable_index: VariableIndex,
        value: InstructionId,
    ) -> Result<(), CodeGenError> {
        let var_pointer = self.get_variable(variable_index)?;

        match operand_type {
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => {
                self.builder
                    .build_store(var_pointer, self.get_int_value(value)?)?;
            }
            Type::Bool => {
                self.builder
                    .build_store(var_pointer, self.get_bool_value(value)?)?;
            }
            Type::F32 | Type::F64 => {
                self.builder
                    .build_store(var_pointer, self.get_float_value(value)?)?;
            }
        };
        Ok(())
    }

    fn handle_let(
        &self,
        variable_index: VariableIndex,
        operand_type: &Type,
        initializer: InstructionId,
    ) -> Result<(), CodeGenError> {
        let var_pointer = self.get_variable(variable_index)?;

        let initializer_value: BasicValueEnum = match operand_type {
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => self.get_int_value(initializer)?.into(),
            Type::Bool => self.get_bool_value(initializer)?.into(),
            Type::F32 | Type::F64 => self.get_float_value(initializer)?.into(),
        };

        self.builder.build_store(var_pointer, initializer_value)?;
        Ok(())
    }

    fn make_fun_type(&self) -> FunctionType<'c> {
        let arguments = self
            .function
            .signature
            .arguments
            .iter()
            .map(|arg| self.llvm_type(&arg.argument_type))
            .collect::<Vec<_>>();

        match &self.function.signature.return_type {
            None => self.context.void_type().fn_type(&arguments, false),
            Some(t) => {
                if t.is_integer() || *t == Type::Bool {
                    self.llvm_int_type(t).fn_type(&arguments, false)
                } else {
                    self.llvm_float_type(t).fn_type(&arguments, false)
                }
            }
        }
    }

    fn setup_fun_arg(&self, fun: FunctionValue<'c>) -> Result<(), CodeGenError> {
        for (i, arg) in self.function.signature.arguments.iter().enumerate() {
            let arg_value =
                fun.get_nth_param(i as u32)
                    .ok_or_else(|| CodeGenError::InternalError {
                        message: format!("Function argument {} not found", i),
                    })?;
            arg_value.set_name(safe_resolve_string_id(arg.name)?);
        }
        Ok(())
    }

    fn handle_binary(
        &self,
        id: InstructionId,
        operator: &BinaryOperator,
        operand_type: &Type,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => {
                self.handle_binary_int_operands(id, operator, left, right)?;
            }
            Type::Bool => {
                self.handle_binary_bool_operands(id, operator, left, right)?;
            }
            Type::F32 | Type::F64 => {
                self.handle_binary_float_operands(id, operator, left, right)?;
            }
        }
        Ok(())
    }

    fn handle_binary_bool_operands(
        &self,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self.get_bool_value(left)?;
        let right = self.get_bool_value(right)?;
        let result = match operator {
            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Rem
            | BinaryOperator::Exp
            | BinaryOperator::Lt
            | BinaryOperator::Lte
            | BinaryOperator::Gt
            | BinaryOperator::Gte
            | BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseOr
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseShl
            | BinaryOperator::BitwiseShr => unreachable!(),

            BinaryOperator::Eq => self.builder.build_int_compare(
                IntPredicate::EQ,
                left,
                right,
                &Self::name("eq", id),
            )?,
            BinaryOperator::Neq => self.builder.build_int_compare(
                IntPredicate::NE,
                left,
                right,
                &Self::name("neq", id),
            )?,
            BinaryOperator::And => self
                .builder
                .build_and(left, right, &Self::name("and", id))?,
            BinaryOperator::Or => self.builder.build_or(left, right, &Self::name("or", id))?,
        };

        self.store_value(id, result.as_basic_value_enum());
        Ok(())
    }

    fn handle_binary_int_operands(
        &self,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self.get_int_value(left)?;
        let right = self.get_int_value(right)?;
        let result = match operator {
            BinaryOperator::Add => {
                self.builder
                    .build_int_add(left, right, &Self::name("add", id))?
            }
            BinaryOperator::Sub => {
                self.builder
                    .build_int_sub(left, right, &Self::name("sub", id))?
            }
            BinaryOperator::Mul => {
                self.builder
                    .build_int_mul(left, right, &Self::name("mul", id))?
            }
            BinaryOperator::Div => {
                self.builder
                    .build_int_signed_div(left, right, &Self::name("div", id))?
            }
            BinaryOperator::Rem => {
                self.builder
                    .build_int_signed_rem(left, right, &Self::name("rem", id))?
            }
            BinaryOperator::Exp => {
                todo!()
            }
            BinaryOperator::Eq => self.builder.build_int_compare(
                IntPredicate::EQ,
                left,
                right,
                &Self::name("eq", id),
            )?,
            BinaryOperator::Neq => self.builder.build_int_compare(
                IntPredicate::NE,
                left,
                right,
                &Self::name("neq", id),
            )?,
            BinaryOperator::Lt => self.builder.build_int_compare(
                IntPredicate::SLT,
                left,
                right,
                &Self::name("lt", id),
            )?,
            BinaryOperator::Lte => self.builder.build_int_compare(
                IntPredicate::SLE,
                left,
                right,
                &Self::name("lte", id),
            )?,
            BinaryOperator::Gt => self.builder.build_int_compare(
                IntPredicate::SGT,
                left,
                right,
                &Self::name("gt", id),
            )?,
            BinaryOperator::Gte => self.builder.build_int_compare(
                IntPredicate::SGE,
                left,
                right,
                &Self::name("gte", id),
            )?,
            BinaryOperator::BitwiseAnd => {
                self.builder
                    .build_and(left, right, &Self::name("bitwise_and", id))?
            }
            BinaryOperator::BitwiseOr => {
                self.builder
                    .build_or(left, right, &Self::name("bitwise_or", id))?
            }
            BinaryOperator::BitwiseXor => {
                self.builder
                    .build_xor(left, right, &Self::name("bitwise_xor", id))?
            }
            BinaryOperator::BitwiseShl => {
                self.builder
                    .build_left_shift(left, right, &Self::name("bitwise_shl", id))?
            }
            BinaryOperator::BitwiseShr => self.builder.build_right_shift(
                left,
                right,
                false,
                &Self::name("bitwise_shr", id),
            )?,

            BinaryOperator::And | BinaryOperator::Or => {
                unreachable!()
            }
        };

        self.store_value(id, result.as_basic_value_enum());
        Ok(())
    }

    fn handle_binary_float_operands(
        &self,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self.get_float_value(left)?;
        let right = self.get_float_value(right)?;

        match operator {
            BinaryOperator::Add => {
                let result = self
                    .builder
                    .build_float_add(left, right, &Self::name("add", id))?;
                self.store_value(id, result.as_basic_value_enum());
            }
            BinaryOperator::Sub => {
                let result = self
                    .builder
                    .build_float_sub(left, right, &Self::name("sub", id))?;
                self.store_value(id, result.as_basic_value_enum());
            }
            BinaryOperator::Mul => {
                let result = self
                    .builder
                    .build_float_mul(left, right, &Self::name("mul", id))?;
                self.store_value(id, result.as_basic_value_enum());
            }
            BinaryOperator::Div => {
                let result = self
                    .builder
                    .build_float_div(left, right, &Self::name("div", id))?;
                self.store_value(id, result.as_basic_value_enum());
            }
            BinaryOperator::Rem => {
                let result = self
                    .builder
                    .build_float_rem(left, right, &Self::name("rem", id))?;
                self.store_value(id, result.as_basic_value_enum());
            }
            BinaryOperator::Eq
            | BinaryOperator::Neq
            | BinaryOperator::Lt
            | BinaryOperator::Lte
            | BinaryOperator::Gt
            | BinaryOperator::Gte => {
                let predicate = match operator {
                    BinaryOperator::Eq => FloatPredicate::OEQ,
                    BinaryOperator::Neq => FloatPredicate::ONE,
                    BinaryOperator::Lt => FloatPredicate::OLT,
                    BinaryOperator::Lte => FloatPredicate::OLE,
                    BinaryOperator::Gt => FloatPredicate::OGT,
                    BinaryOperator::Gte => FloatPredicate::OGE,
                    _ => unreachable!(),
                };
                let result = self.builder.build_float_compare(
                    predicate,
                    left,
                    right,
                    &Self::name("fcmp", id),
                )?;
                self.store_value(id, result.as_basic_value_enum());
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn handle_unary(
        &self,
        id: InstructionId,
        operand_type: &Type,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => {
                self.handle_unary_int_operand(id, operator, operand)?;
            }
            Type::Bool => {
                self.handle_unary_bool_operand(id, operator, operand)?;
            }
            Type::F32 | Type::F64 => {
                self.handle_unary_float_operand(id, operator, operand)?;
            }
        }
        Ok(())
    }

    fn handle_unary_bool_operand(
        &self,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self.get_bool_value(operand)?;
        let result = match operator {
            UnaryOperator::Neg | UnaryOperator::BitwiseNot => {
                unreachable!()
            }
            UnaryOperator::Not => self.builder.build_not(operand, &Self::name("not", id))?,
        };

        self.store_value(id, result.as_basic_value_enum());
        Ok(())
    }

    fn handle_unary_int_operand(
        &self,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self.get_int_value(operand)?;
        let result = match operator {
            UnaryOperator::Neg => self
                .builder
                .build_int_neg(operand, &Self::name("neg", id))?,
            UnaryOperator::BitwiseNot => {
                // There's no LLVM instruction for bitwise not, but we can xor with
                // all 1s to get the same result (i.e. complement to 1)
                self.builder.build_xor(
                    self.context.i64_type().const_all_ones(),
                    operand,
                    &Self::name("bitwise_not", id),
                )?
            }
            UnaryOperator::Not => {
                unreachable!("unexpected not operator with i32 type")
            }
        };

        self.store_value(id, result.as_basic_value_enum());
        Ok(())
    }

    fn handle_unary_float_operand(
        &self,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self.get_float_value(operand)?;
        let result = match operator {
            UnaryOperator::Neg => self
                .builder
                .build_float_neg(operand, &Self::name("neg", id))?,
            UnaryOperator::Not | UnaryOperator::BitwiseNot => {
                unreachable!()
            }
        };

        self.store_value(id, result.as_basic_value_enum());
        Ok(())
    }

    fn handle_constant(&self, id: InstructionId, constant: &LiteralValue) {
        let value = match constant {
            LiteralValue::I8(value) => self
                .context
                .i8_type()
                .const_int(*value as u64, false)
                .as_basic_value_enum(),
            LiteralValue::I16(value) => self
                .context
                .i16_type()
                .const_int(*value as u64, false)
                .as_basic_value_enum(),
            LiteralValue::I32(value) => self
                .context
                .i32_type()
                .const_int(*value as u64, false)
                .as_basic_value_enum(),
            LiteralValue::I64(value) => self
                .context
                .i64_type()
                .const_int(*value as u64, false)
                .as_basic_value_enum(),
            LiteralValue::F32(value) => self
                .context
                .f32_type()
                .const_float(*value as f64)
                .as_basic_value_enum(),
            LiteralValue::F64(value) => self
                .context
                .f64_type()
                .const_float(*value)
                .as_basic_value_enum(),
            LiteralValue::Boolean(value) => self
                .context
                .bool_type()
                .const_int(if *value { 1 } else { 0 }, false)
                .as_basic_value_enum(),
        };
        self.store_value(id, value);
    }

    fn handle_return_expression(
        &self,
        expression: InstructionId,
        operand_type: &Type,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::I8 | Type::I16 | Type::I32 | Type::I64 => {
                let operand = self.get_int_value(expression)?;
                self.builder.build_return(Some(&operand))?;
            }
            Type::Bool => {
                let operand = self.get_bool_value(expression)?;
                self.builder.build_return(Some(&operand))?;
            }
            Type::F32 | Type::F64 => {
                let operand = self.get_float_value(expression)?;
                self.builder.build_return(Some(&operand))?;
            }
        }
        Ok(())
    }

    fn handle_function_call(
        &self,
        id: InstructionId,
        llvm_module: &Module<'c>,
        function_name: &StringId,
        return_type: &Option<Type>,
        arguments: &[InstructionId],
    ) -> Result<(), CodeGenError> {
        // Get the function name
        let function_name_str = safe_resolve_string_id(*function_name)?;

        // Look up the function in the LLVM module
        let function = llvm_module.get_function(function_name_str).ok_or_else(|| {
            CodeGenError::InternalError {
                message: format!("Function '{}' not found in module", function_name_str),
            }
        })?;

        // Prepare argument values
        let mut argument_values = Vec::new();
        for &arg_id in arguments {
            argument_values.push(self.get_value(arg_id)?.into());
        }

        // Call the function
        let call_site =
            self.builder
                .build_call(function, &argument_values, &Self::name("call", id))?;

        // Handle return value
        match return_type {
            Some(_) => {
                // Function returns a value, store it
                let return_value = call_site.try_as_basic_value().left().ok_or_else(|| {
                    CodeGenError::InternalError {
                        message: "Expected function to return a value".to_string(),
                    }
                })?;
                self.store_value(id, return_value);
            }
            None => {
                // Void function, no return value to store
            }
        }

        Ok(())
    }

    fn handle_jump(&self, target_block: BlockId) -> Result<(), CodeGenError> {
        let target_bb = *self
            .llvm_blocks
            .borrow()
            .get(&target_block)
            .ok_or_else(|| CodeGenError::InternalError {
                message: format!("Target block {} not found", target_block.0),
            })?;
        self.builder.build_unconditional_branch(target_bb)?;
        Ok(())
    }

    fn handle_branch(
        &self,
        condition: InstructionId,
        then_block: BlockId,
        else_block: BlockId,
    ) -> Result<(), CodeGenError> {
        let condition_value = self.get_bool_value(condition)?;
        let then_bb = *self.llvm_blocks.borrow().get(&then_block).ok_or_else(|| {
            CodeGenError::InternalError {
                message: format!("Then block {} not found", then_block.0),
            }
        })?;
        let else_bb = *self.llvm_blocks.borrow().get(&else_block).ok_or_else(|| {
            CodeGenError::InternalError {
                message: format!("Else block {} not found", else_block.0),
            }
        })?;

        self.builder
            .build_conditional_branch(condition_value, then_bb, else_bb)?;
        Ok(())
    }

    fn name(prefix: &str, id: InstructionId) -> String {
        format!("{}_{}", prefix, id)
    }
}

struct LlvmGenerator<'c, 'ir, 'ir2>
where
    'c: 'ir,
{
    context: &'c Context,
    builder: Builder<'c>,
    ir_module: &'ir codegen::Module<'ir2>,
}

impl<'c, 'm, 'm2> LlvmGenerator<'c, 'm, 'm2> {
    fn new(context: &'c Context, ir_module: &'m codegen::Module<'m2>) -> Self {
        let builder = context.create_builder();
        Self {
            context,
            builder,
            ir_module,
        }
    }

    fn generate(&self) -> Result<Module<'c>, CodeGenError> {
        let llvm_module = self
            .context
            .create_module(safe_resolve_string_id(self.ir_module.name)?);

        // Pass 1: Declare all functions
        let mut declared_functions = Vec::new();
        for function in self.ir_module.functions.iter() {
            let fun_generator = LlvmFunctionGenerator::new(self.context, &self.builder, function);
            let llvm_function = fun_generator.declare(&llvm_module)?;
            declared_functions.push((fun_generator, llvm_function));
        }

        // Pass 2: Generate function bodies
        for (fun_generator, llvm_function) in declared_functions {
            fun_generator.generate_body(llvm_function, &llvm_module)?;
        }

        Ok(llvm_module)
    }
}

#[allow(unused)]
pub fn ir_to_llvm<'c>(
    context: &'c Context,
    module: &codegen::Module,
) -> Result<Module<'c>, CodeGenError> {
    let mut builder = LlvmGenerator::new(context, module);
    builder.generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::IrAllocator;
    use codegen::build_ir_module;
    use inkwell::context::Context;
    use semantic_analysis::{PhaseTypeResolved, SemanticAnalyzer};
    use std::io::{Write, stderr};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'s>(
        semantic_analyzer: &'s SemanticAnalyzer,
        source: &str,
    ) -> &'s parser::Module<'s, PhaseTypeResolved<'s>> {
        let ast_allocator = parser::ParsedAstAllocator::default();
        let module = parser::parse(&ast_allocator, "test", source).expect("parse should succeed");

        let result = semantic_analyzer.analyze_module(module);
        result.expect("should have passed semantic analysis")
    }

    fn handle_module<'i>(ir_allocator: &'i IrAllocator, source: &str) -> &'i codegen::Module<'i> {
        let semantic_analyzer = SemanticAnalyzer::default();
        let module = make_analyzed_ast(&semantic_analyzer, source);
        let module = build_ir_module(ir_allocator, module).expect("codegen should succeed");

        eprintln!("Module IR:\n{}", module);
        stderr().flush().unwrap();

        module
    }

    fn compile_function_to_llvm(function_source: &str) -> String {
        let ir_allocator = IrAllocator::new();
        let module = handle_module(&ir_allocator, function_source);
        let context = Context::create();
        ir_to_llvm(&context, module).unwrap().to_string()
    }

    #[test]
    fn test_empty_function() {
        let llvm_ir = compile_function_to_llvm("fn empty() { }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @empty() {
        bb0:
          ret void
        }
        "#);
    }

    #[test]
    fn test_add_one_function() {
        let llvm_ir = compile_function_to_llvm("fn add_one(x: i32) -> i32 { return 1i32 + x; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @add_one(i32 %x) {
        bb0:
          %add_2 = add i32 1, %x
          ret i32 %add_2
        }
        "#);
    }

    #[test]
    fn test_add_one_float_function() {
        let llvm_ir = compile_function_to_llvm("fn add(x: f64, y: f64) -> f64 { return x + y; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define double @add(double %x, double %y) {
        bb0:
          %add_2 = fadd double %x, %y
          ret double %add_2
        }
        "#);
    }

    #[test]
    fn test_neg_float_function() {
        let llvm_ir = compile_function_to_llvm("fn neg(x: f64) -> f64 { return -x; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define double @neg(double %x) {
        bb0:
          %neg_1 = fneg double %x
          ret double %neg_1
        }
        "#);
    }

    #[test]
    fn test_comparison_int() {
        let llvm_ir =
            compile_function_to_llvm("fn greater(x: i32, y: i32) -> bool { return x > y; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i1 @greater(i32 %x, i32 %y) {
        bb0:
          %gt_2 = icmp sgt i32 %x, %y
          ret i1 %gt_2
        }
        "#);
    }

    #[test]
    fn test_comparison_float() {
        let llvm_ir =
            compile_function_to_llvm("fn greater(x: f64, y: f64) -> bool { return x > y; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i1 @greater(double %x, double %y) {
        bb0:
          %fcmp_2 = fcmp ogt double %x, %y
          ret i1 %fcmp_2
        }
        "#);
    }

    #[test]
    fn test_declare_var_function() {
        let llvm_ir = compile_function_to_llvm("fn declare_var() { let x = 1i32; let y = true; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @declare_var() {
        bb0:
          %x = alloca i32, align 4
          %y = alloca i1, align 1
          store i32 1, ptr %x, align 4
          store i1 true, ptr %y, align 1
          ret void
        }
        "#);
    }

    #[test]
    fn test_use_var_function() {
        let llvm_ir = compile_function_to_llvm(
            "fn use_var() -> bool { let x = false; let y = true; return y && !x; }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i1 @use_var() {
        bb0:
          %x = alloca i1, align 1
          %"$temp0" = alloca i1, align 1
          %y = alloca i1, align 1
          store i1 false, ptr %x, align 1
          store i1 true, ptr %"$temp0", align 1
          %load_4 = load i1, ptr %"$temp0", align 1
          store i1 %load_4, ptr %x, align 1
          br i1 %load_4, label %bb1, label %bb2

        bb1:                                              ; preds = %bb0
          %load_7 = load i1, ptr %x, align 1
          %not_8 = xor i1 %load_7, true
          store i1 %not_8, ptr %x, align 1
          br label %bb2

        bb2:                                              ; preds = %bb1, %bb0
          %load_11 = load i1, ptr %x, align 1
          ret i1 %load_11
        }
        "#);
    }

    #[test]
    fn test_set_var_function() {
        let llvm_ir = compile_function_to_llvm(
            "fn set_var() { let x = 0i32; x = 1i32; let y = false; y = true; }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @set_var() {
        bb0:
          %x = alloca i32, align 4
          %y = alloca i1, align 1
          store i32 0, ptr %x, align 4
          store i32 1, ptr %x, align 4
          store i1 false, ptr %y, align 1
          store i1 true, ptr %y, align 1
          ret void
        }
        "#);
    }

    #[test]
    fn test_float_variable() {
        let llvm_ir = compile_function_to_llvm(
            "fn vars() -> f64 { let x = 1.0f64; let y = 2.0f64; return x + y; }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define double @vars() {
        bb0:
          %x = alloca double, align 8
          %y = alloca double, align 8
          store double 1.000000e+00, ptr %x, align 8
          store double 2.000000e+00, ptr %y, align 8
          %load_4 = load double, ptr %x, align 8
          %load_5 = load double, ptr %y, align 8
          %add_6 = fadd double %load_4, %load_5
          ret double %add_6
        }
        "#);
    }

    #[test]
    fn test_set_param_function() {
        let llvm_ir =
            compile_function_to_llvm("fn set_param(x: i32) -> i32 { x = x + 1; return x; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @set_param(i32 %x) {
        bb0:
          %x1 = alloca i32, align 4
          %add_2 = add i32 %x, 1
          store i32 %add_2, ptr %x1, align 4
          %load_4 = load i32, ptr %x1, align 4
          ret i32 %load_4
        }
        "#);
    }

    #[test]
    fn test_function_call_no_args() {
        let llvm_ir = compile_function_to_llvm(
            r"fn get_five() -> i32 { return 5; }
            fn main() -> i32 { return get_five(); }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @get_five() {
        bb0:
          ret i32 5
        }

        define i32 @main() {
        bb0:
          %call_0 = call i32 @get_five()
          ret i32 %call_0
        }
        "#);
    }

    #[test]
    fn test_function_call_with_args() {
        let llvm_ir = compile_function_to_llvm(
            r"fn add(x: i32, y: i32) -> i32 { return x + y; }
            fn main() -> i32 { return add(3, 7); }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @add(i32 %x, i32 %y) {
        bb0:
          %add_2 = add i32 %x, %y
          ret i32 %add_2
        }

        define i32 @main() {
        bb0:
          %call_2 = call i32 @add(i32 3, i32 7)
          ret i32 %call_2
        }
        "#);
    }

    #[test]
    fn test_function_call_void() {
        let llvm_ir = compile_function_to_llvm(
            r"fn print_hello() { }
        fn main() { print_hello(); }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @print_hello() {
        bb0:
          ret void
        }

        define void @main() {
        bb0:
          call void @print_hello()
          ret void
        }
        "#);
    }

    #[test]
    fn test_function_call_before_definition() {
        let llvm_ir = compile_function_to_llvm(
            r"
        fn main() { callee(); }
        fn callee() { }
        ",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @main() {
        bb0:
          call void @callee()
          ret void
        }

        define void @callee() {
        bb0:
          ret void
        }
        "#);
    }

    #[test]
    fn test_if_statement_simple() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test(x: bool) -> i32 {
                if x {
                    return 1;
                }
                return 0;
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @test(i1 %x) {
        bb0:
          br i1 %x, label %bb2, label %bb1

        bb2:                                              ; preds = %bb0
          ret i32 1

        bb1:                                              ; preds = %bb0
          ret i32 0
        }
        "#);
    }

    #[test]
    fn test_if_statement_with_else() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test(x: bool) -> i32 {
                if x {
                    return 1;
                } else {
                    return 0;
                }
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @test(i1 %x) {
        bb0:
          br i1 %x, label %bb2, label %bb3

        bb2:                                              ; preds = %bb0
          ret i32 1

        bb3:                                              ; preds = %bb0
          ret i32 0
        }
        "#);
    }

    #[test]
    fn test_if_elseif_else() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test(x: i32) -> i32 {
                if x > 0 {
                    return 1;
                } else if x < 0 {
                    return -1;
                } else {
                    return 0;
                }
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @test(i32 %x) {
        bb0:
          %gt_2 = icmp sgt i32 %x, 0
          br i1 %gt_2, label %bb2, label %bb3

        bb2:                                              ; preds = %bb0
          ret i32 1

        bb3:                                              ; preds = %bb0
          %lt_8 = icmp slt i32 %x, 0
          br i1 %lt_8, label %bb4, label %bb5

        bb4:                                              ; preds = %bb3
          ret i32 -1

        bb5:                                              ; preds = %bb3
          ret i32 0
        }
        "#);
    }

    #[test]
    fn test_if_statement_variable_assignment() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test(condition: bool) -> i32 {
                let result = 0i32;
                if condition {
                    result = 42;
                }
                return result;
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @test(i1 %condition) {
        bb0:
          %result = alloca i32, align 4
          store i32 0, ptr %result, align 4
          br i1 %condition, label %bb2, label %bb1

        bb2:                                              ; preds = %bb0
          store i32 42, ptr %result, align 4
          br label %bb1

        bb1:                                              ; preds = %bb2, %bb0
          %load_7 = load i32, ptr %result, align 4
          ret i32 %load_7
        }
        "#);
    }

    #[test]
    fn test_nested_if_statements() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test(x: i32, y: i32) -> i32 {
                if x > 0 {
                    if y > 0 {
                        return 1;
                    } else {
                        return 2;
                    }
                } else {
                    return 3;
                }
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @test(i32 %x, i32 %y) {
        bb0:
          %gt_2 = icmp sgt i32 %x, 0
          br i1 %gt_2, label %bb2, label %bb3

        bb2:                                              ; preds = %bb0
          %gt_6 = icmp sgt i32 %y, 0
          br i1 %gt_6, label %bb5, label %bb6

        bb3:                                              ; preds = %bb0
          ret i32 3

        bb5:                                              ; preds = %bb2
          ret i32 1

        bb6:                                              ; preds = %bb2
          ret i32 2
        }
        "#);
    }

    #[test]
    fn test_variable_declared_in_if_block() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test(condition: bool) -> i32 {
                if condition {
                    let x = 42;
                    return x;
                }
                return 0;
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i32 @test(i1 %condition) {
        bb0:
          %x = alloca i32, align 4
          br i1 %condition, label %bb2, label %bb1

        bb2:                                              ; preds = %bb0
          store i32 42, ptr %x, align 4
          %load_4 = load i32, ptr %x, align 4
          ret i32 %load_4

        bb1:                                              ; preds = %bb0
          ret i32 0
        }
        "#);
    }

    #[test]
    fn test_break_in_while_loop() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test() {
                while true {
                    break;
                }
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @test() {
        bb0:
          br label %bb1

        bb1:                                              ; preds = %bb0
          br i1 true, label %bb2, label %bb3

        bb2:                                              ; preds = %bb1
          br label %bb3

        bb3:                                              ; preds = %bb2, %bb1
          ret void
        }
        "#);
    }

    #[test]
    fn test_continue_in_while_loop() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test() {
                while true {
                    continue;
                }
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @test() {
        bb0:
          br label %bb1

        bb1:                                              ; preds = %bb2, %bb0
          br i1 true, label %bb2, label %bb3

        bb2:                                              ; preds = %bb1
          br label %bb1

        bb3:                                              ; preds = %bb1
          ret void
        }
        "#);
    }

    #[test]
    fn test_nested_loops_with_break_continue() {
        let llvm_ir = compile_function_to_llvm(
            r"fn test() {
                while true {
                    while true {
                        break;
                    }
                    continue;
                }
            }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @test() {
        bb0:
          br label %bb1

        bb1:                                              ; preds = %bb6, %bb0
          br i1 true, label %bb2, label %bb3

        bb2:                                              ; preds = %bb1
          br label %bb4

        bb4:                                              ; preds = %bb2
          br i1 true, label %bb5, label %bb6

        bb5:                                              ; preds = %bb4
          br label %bb6

        bb6:                                              ; preds = %bb5, %bb4
          br label %bb1

        bb3:                                              ; preds = %bb1
          ret void
        }
        "#);
    }
}
