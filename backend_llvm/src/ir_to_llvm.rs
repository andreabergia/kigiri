use codegen::{Function, Instruction, InstructionId, InstructionPayload, LiteralValue};
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::FunctionType;
use inkwell::values::{
    BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue, PointerValue,
};
use inkwell::{FloatPredicate, IntPredicate};
use parser::{BinaryOperator, UnaryOperator, resolve_string_id};
use semantic_analysis::{ArgumentIndex, Type, VariableIndex};
use std::cell::RefCell;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
#[error("Code generation error: {message}")]
pub struct CodeGenError {
    message: String,
}

impl From<BuilderError> for CodeGenError {
    fn from(value: BuilderError) -> Self {
        Self {
            message: value.to_string(),
        }
    }
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
}

impl<'c, 'c2, 'ir, 'ir2> LlvmFunctionGenerator<'c, 'c2, 'ir, 'ir2> {
    fn new(context: &'c Context, builder: &'c2 Builder<'c>, function: &'ir Function<'ir2>) -> Self {
        let first_block = function
            .basic_blocks
            .first()
            .expect("function must have at least one basic block");
        let num_instructions = first_block.instructions.borrow().len();

        let mut llvm_values = Vec::with_capacity(num_instructions);
        llvm_values.resize(num_instructions, None);

        let variables = Vec::with_capacity(first_block.variables.borrow().len());

        Self {
            context,
            builder,
            function,
            llvm_values: llvm_values.into(),
            variables: variables.into(),
        }
    }

    fn alloca_variables(&self) -> Result<(), CodeGenError> {
        let first_block = self
            .function
            .basic_blocks
            .first()
            .expect("function must have at least one basic block");
        for var in first_block.variables.borrow().iter() {
            let name = resolve_string_id(var.name).expect("variable name");
            let value = match var.variable_type {
                Type::Int => self.builder.build_alloca(self.context.i64_type(), name)?,
                Type::Bool => self.builder.build_alloca(self.context.bool_type(), name)?,
                Type::Double => self.builder.build_alloca(self.context.f64_type(), name)?,
            };
            self.variables.borrow_mut().push(value);
        }
        Ok(())
    }

    fn store_value(&self, id: InstructionId, value: BasicValueEnum<'c>) {
        self.llvm_values.borrow_mut()[id.as_usize()] = Some(value);
    }

    fn get_int_value(&self, id: InstructionId) -> IntValue<'c> {
        self.get_value(id).into_int_value()
    }

    fn get_bool_value(&self, id: InstructionId) -> IntValue<'c> {
        self.get_value(id).into_int_value()
    }

    fn get_float_value(&self, id: InstructionId) -> FloatValue<'c> {
        self.get_value(id).into_float_value()
    }

    fn get_value(&self, id: InstructionId) -> BasicValueEnum<'c> {
        self.llvm_values
            .borrow()
            .get(id.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("value should be present")
    }

    fn declare(&self, llvm_module: &Module<'c>) -> Result<FunctionValue<'c>, CodeGenError> {
        let fn_type = self.make_fun_type();
        let fun = llvm_module.add_function(
            resolve_string_id(self.function.signature.name).expect("function name"),
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
        let bb = self.context.append_basic_block(fun, "entry");
        self.builder.position_at_end(bb);

        self.alloca_variables()?;

        let first_block = self
            .function
            .basic_blocks
            .first()
            .expect("function must have at least one basic block");
        for instruction in first_block.instructions.borrow().iter() {
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
                InstructionPayload::LoadArg {
                    operand_type,
                    argument_index,
                    ..
                } => {
                    self.handle_load_arg(fun, instruction, operand_type, *argument_index)?;
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
                InstructionPayload::Jump { .. } => {
                    todo!("Jump instructions not implemented in LLVM backend yet")
                }
                InstructionPayload::Branch { .. } => {
                    todo!("Branch instructions not implemented in LLVM backend yet")
                }
            }
        }

        if !fun.verify(true) {
            panic!("LLVM says we have built an invalid function; this is a bug :-(");
        }
        Ok(())
    }

    fn handle_load_var(
        &self,
        instruction: &Instruction,
        operand_type: &Type,
        variable_index: VariableIndex,
    ) -> Result<(), CodeGenError> {
        let variable_index: usize = variable_index.into();
        let var_pointer = *self
            .variables
            .borrow()
            .get(variable_index)
            .expect("variable index should be valid");

        match operand_type {
            Type::Int => {
                self.store_value(
                    instruction.id,
                    self.builder.build_load(
                        self.context.i64_type(),
                        var_pointer,
                        &Self::name("load", instruction.id),
                    )?,
                );
            }
            Type::Bool => {
                self.store_value(
                    instruction.id,
                    self.builder.build_load(
                        self.context.bool_type(),
                        var_pointer,
                        &Self::name("load", instruction.id),
                    )?,
                );
            }
            Type::Double => {
                self.store_value(
                    instruction.id,
                    self.builder.build_load(
                        self.context.f64_type(),
                        var_pointer,
                        &Self::name("load", instruction.id),
                    )?,
                );
            }
        };
        Ok(())
    }

    fn handle_load_arg(
        &self,
        fun: FunctionValue<'c>,
        instruction: &Instruction,
        operand_type: &Type,
        argument_index: ArgumentIndex,
    ) -> Result<(), CodeGenError> {
        let value = fun
            .get_nth_param(argument_index.into())
            .expect("valid argument number");
        match operand_type {
            Type::Int => {
                self.store_value(instruction.id, value);
            }
            Type::Bool => {
                self.store_value(instruction.id, value);
            }
            Type::Double => {
                self.store_value(instruction.id, value);
            }
        };
        Ok(())
    }

    fn handle_store_var(
        &self,
        operand_type: &Type,
        variable_index: VariableIndex,
        value: InstructionId,
    ) -> Result<(), CodeGenError> {
        let variable_index: usize = variable_index.into();
        let var_pointer = *self
            .variables
            .borrow()
            .get(variable_index)
            .expect("variable index should be valid");

        match operand_type {
            Type::Int => {
                self.builder
                    .build_store(var_pointer, self.get_int_value(value))?;
            }
            Type::Bool => {
                self.builder
                    .build_store(var_pointer, self.get_bool_value(value))?;
            }
            Type::Double => {
                self.builder
                    .build_store(var_pointer, self.get_float_value(value))?;
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
        let variable_index: usize = variable_index.into();
        let var_pointer = *self
            .variables
            .borrow()
            .get(variable_index)
            .expect("variable index should be valid");

        let initializer_value: BasicValueEnum = match operand_type {
            Type::Int => self.get_int_value(initializer).into(),
            Type::Bool => self.get_bool_value(initializer).into(),
            Type::Double => self.get_float_value(initializer).into(),
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
            .map(|arg| match arg.argument_type {
                Type::Int => self.context.i64_type().into(),
                Type::Bool => self.context.bool_type().into(),
                Type::Double => self.context.f64_type().into(),
            })
            .collect::<Vec<_>>();

        match &self.function.signature.return_type {
            None => self.context.void_type().fn_type(&arguments, false),
            Some(t) => match t {
                Type::Int => self.context.i64_type().fn_type(&arguments, false),
                Type::Bool => self.context.bool_type().fn_type(&arguments, false),
                Type::Double => self.context.f64_type().fn_type(&arguments, false),
            },
        }
    }

    fn setup_fun_arg(&self, fun: FunctionValue<'c>) -> Result<(), CodeGenError> {
        for (i, arg) in self.function.signature.arguments.iter().enumerate() {
            let arg_value = fun.get_nth_param(i as u32).expect("should have argument");
            arg_value.set_name(resolve_string_id(arg.name).expect("function argument name"));
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
            Type::Int => {
                self.handle_binary_int_operands(id, operator, left, right)?;
            }
            Type::Bool => {
                self.handle_binary_bool_operands(id, operator, left, right)?;
            }
            Type::Double => {
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
        let left = self.get_bool_value(left);
        let right = self.get_bool_value(right);
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
        let left = self.get_int_value(left);
        let right = self.get_int_value(right);
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
                todo!()
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
        let left = self.get_float_value(left);
        let right = self.get_float_value(right);

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
            Type::Int => {
                self.handle_unary_int_operand(id, operator, operand)?;
            }
            Type::Bool => {
                self.handle_unary_bool_operand(id, operator, operand)?;
            }
            Type::Double => {
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
        let operand = self.get_bool_value(operand);
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
        let operand = self.get_int_value(operand);
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
                unreachable!("unexpected not operator with int type")
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
        let operand = self.get_float_value(operand);
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
            LiteralValue::Integer(value) => self
                .context
                .i64_type()
                .const_int(*value as u64, false)
                .as_basic_value_enum(),
            LiteralValue::Boolean(value) => self
                .context
                .bool_type()
                .const_int(if *value { 1 } else { 0 }, false)
                .as_basic_value_enum(),
            LiteralValue::Double(value) => self
                .context
                .f64_type()
                .const_float(*value)
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
            Type::Int => {
                let operand = self.get_int_value(expression);
                self.builder.build_return(Some(&operand))?;
            }
            Type::Bool => {
                let operand = self.get_bool_value(expression);
                self.builder.build_return(Some(&operand))?;
            }
            Type::Double => {
                let operand = self.get_float_value(expression);
                self.builder.build_return(Some(&operand))?;
            }
        }
        Ok(())
    }

    fn handle_function_call(
        &self,
        id: InstructionId,
        llvm_module: &Module<'c>,
        function_name: &parser::StringId,
        return_type: &Option<Type>,
        arguments: &[InstructionId],
    ) -> Result<(), CodeGenError> {
        // Get the function name
        let function_name_str = resolve_string_id(*function_name).expect("function name");

        // Look up the function in the LLVM module
        let function = llvm_module
            .get_function(function_name_str)
            .ok_or_else(|| CodeGenError {
                message: format!("Function '{}' not found in module", function_name_str),
            })?;

        // Prepare argument values
        let mut argument_values = Vec::new();
        for &arg_id in arguments {
            argument_values.push(self.get_value(arg_id).into());
        }

        // Call the function
        let call_site =
            self.builder
                .build_call(function, &argument_values, &Self::name("call", id))?;

        // Handle return value
        match return_type {
            Some(_) => {
                // Function returns a value, store it
                let return_value =
                    call_site
                        .try_as_basic_value()
                        .left()
                        .ok_or_else(|| CodeGenError {
                            message: "Expected function to return a value".to_string(),
                        })?;
                self.store_value(id, return_value);
            }
            None => {
                // Void function, no return value to store
            }
        }

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
            .create_module(resolve_string_id(self.ir_module.name).expect("module name"));

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
        let module = parser::parse(&ast_allocator, "test", source);

        let result = semantic_analyzer.analyze_module(module);
        result.expect("should have passed semantic analysis")
    }

    fn handle_module<'i>(ir_allocator: &'i IrAllocator, source: &str) -> &'i codegen::Module<'i> {
        let semantic_analyzer = SemanticAnalyzer::default();
        let module = make_analyzed_ast(&semantic_analyzer, source);
        let module = build_ir_module(ir_allocator, module);

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
        entry:
          ret void
        }
        "#);
    }

    #[test]
    fn test_add_one_function() {
        let llvm_ir = compile_function_to_llvm("fn add_one(x: int) -> int { return 1 + x; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i64 @add_one(i64 %x) {
        entry:
          %add_2 = add i64 1, %x
          ret i64 %add_2
        }
        "#);
    }

    #[test]
    fn test_add_one_float_function() {
        let llvm_ir =
            compile_function_to_llvm("fn add(x: double, y: double) -> double { return x + y; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define double @add(double %x, double %y) {
        entry:
          %add_2 = fadd double %x, %y
          ret double %add_2
        }
        "#);
    }

    #[test]
    fn test_neg_float_function() {
        let llvm_ir = compile_function_to_llvm("fn neg(x: double) -> double { return -x; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define double @neg(double %x) {
        entry:
          %neg_1 = fneg double %x
          ret double %neg_1
        }
        "#);
    }

    #[test]
    fn test_comparison_int() {
        let llvm_ir =
            compile_function_to_llvm("fn greater(x: int, y: int) -> bool { return x > y; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i1 @greater(i64 %x, i64 %y) {
        entry:
          %gt_2 = icmp sgt i64 %x, %y
          ret i1 %gt_2
        }
        "#);
    }

    #[test]
    fn test_comparison_float() {
        let llvm_ir =
            compile_function_to_llvm("fn greater(x: double, y: double) -> bool { return x > y; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i1 @greater(double %x, double %y) {
        entry:
          %fcmp_2 = fcmp ogt double %x, %y
          ret i1 %fcmp_2
        }
        "#);
    }

    #[test]
    fn test_declare_var_function() {
        let llvm_ir = compile_function_to_llvm("fn declare_var() { let x = 1; let y = true; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @declare_var() {
        entry:
          %x = alloca i64, align 8
          %y = alloca i1, align 1
          store i64 1, ptr %x, align 4
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
        entry:
          %x = alloca i1, align 1
          %y = alloca i1, align 1
          store i1 false, ptr %x, align 1
          store i1 true, ptr %y, align 1
          %load_4 = load i1, ptr %y, align 1
          %load_5 = load i1, ptr %x, align 1
          %not_6 = xor i1 %load_5, true
          %and_7 = and i1 %load_4, %not_6
          ret i1 %and_7
        }
        "#);
    }

    #[test]
    fn test_set_var_function() {
        let llvm_ir =
            compile_function_to_llvm("fn set_var() { let x = 0; x = 1; let y = false; y = true; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @set_var() {
        entry:
          %x = alloca i64, align 8
          %y = alloca i1, align 1
          store i64 0, ptr %x, align 4
          store i64 1, ptr %x, align 4
          store i1 false, ptr %y, align 1
          store i1 true, ptr %y, align 1
          ret void
        }
        "#);
    }

    #[test]
    fn test_float_variable() {
        let llvm_ir = compile_function_to_llvm(
            "fn vars() -> double { let x = 1.0; let y = 2.0; return x + y; }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define double @vars() {
        entry:
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
            compile_function_to_llvm("fn set_param(x: int) -> int { x = x + 1; return x; }");
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i64 @set_param(i64 %x) {
        entry:
          %x1 = alloca i64, align 8
          %add_2 = add i64 %x, 1
          store i64 %add_2, ptr %x1, align 4
          %load_4 = load i64, ptr %x1, align 4
          ret i64 %load_4
        }
        "#);
    }

    #[test]
    fn test_function_call_no_args() {
        let llvm_ir = compile_function_to_llvm(
            r"fn get_five() -> int { return 5; }
            fn main() -> int { return get_five(); }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i64 @get_five() {
        entry:
          ret i64 5
        }

        define i64 @main() {
        entry:
          %call_0 = call i64 @get_five()
          ret i64 %call_0
        }
        "#);
    }

    #[test]
    fn test_function_call_with_args() {
        let llvm_ir = compile_function_to_llvm(
            r"fn add(x: int, y: int) -> int { return x + y; }
            fn main() -> int { return add(3, 7); }",
        );
        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define i64 @add(i64 %x, i64 %y) {
        entry:
          %add_2 = add i64 %x, %y
          ret i64 %add_2
        }

        define i64 @main() {
        entry:
          %call_2 = call i64 @add(i64 3, i64 7)
          ret i64 %call_2
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
        entry:
          ret void
        }

        define void @main() {
        entry:
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
        entry:
          call void @callee()
          ret void
        }

        define void @callee() {
        entry:
          ret void
        }
        "#);
    }
}
