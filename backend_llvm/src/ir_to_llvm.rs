use codegen::{
    BasicBlock, Function, Instruction, InstructionId, InstructionPayload, LiteralValue,
    VariableIndex,
};
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::FunctionType;
use inkwell::values::{FunctionValue, IntValue, PointerValue};
use inkwell::IntPredicate;
use parser::{resolve_string_id, BinaryOperator, UnaryOperator};
use semantic_analysis::{SymbolKind, Type};
use std::cell::RefCell;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
#[error("Code generation error: {message}")]
struct CodeGenError {
    message: String,
}

impl From<BuilderError> for CodeGenError {
    fn from(value: BuilderError) -> Self {
        Self {
            message: value.to_string(),
        }
    }
}

struct FunctionContext<'c> {
    // Vectors are indexed by instruction id. There's a bit of space wasted,
    // but it makes everything quite simple and fast.
    int_values: RefCell<Vec<Option<IntValue<'c>>>>,
    bool_values: RefCell<Vec<Option<IntValue<'c>>>>,

    // Variables are indexed by their progressive number
    int_bool_variable: RefCell<Vec<PointerValue<'c>>>,
}

impl<'c> FunctionContext<'c> {
    fn new(block: &BasicBlock) -> Self {
        let num_instructions = block.instructions.borrow().len();

        let mut int_values = Vec::with_capacity(num_instructions);
        int_values.resize(num_instructions, None);
        let mut bool_values = Vec::with_capacity(num_instructions);
        bool_values.resize(num_instructions, None);

        let int_bool_variable = Vec::with_capacity(block.variables.borrow().len());

        Self {
            int_values: int_values.into(),
            bool_values: bool_values.into(),
            int_bool_variable: int_bool_variable.into(),
        }
    }

    fn alloca_variables(
        &self,
        block: &BasicBlock,
        context: &'c Context,
        builder: &Builder<'c>,
    ) -> Result<(), CodeGenError> {
        for var in block.variables.borrow().iter() {
            let value = builder.build_alloca(
                match var.variable_type {
                    Type::Int => context.i64_type(),
                    Type::Boolean => context.bool_type(),
                    Type::Double => todo!(),
                },
                resolve_string_id(var.name).expect("variable name"),
            )?;
            self.int_bool_variable.borrow_mut().push(value);
        }
        Ok(())
    }
}

struct LlvmGenerator<'c, 'm, 'm2>
where
    'c: 'm,
{
    context: &'c Context,
    llvm_module: Module<'c>,
    builder: Builder<'c>,
    ir_module: &'m codegen::Module<'m2>,
}

impl<'c, 'm, 'm2> LlvmGenerator<'c, 'm, 'm2> {
    fn new(context: &'c Context, ir_module: &'m codegen::Module<'m2>) -> Self {
        let llvm_module =
            context.create_module(resolve_string_id(ir_module.name).expect("module name"));
        let builder = context.create_builder();
        Self {
            context,
            llvm_module,
            builder,
            ir_module,
        }
    }

    fn generate(&mut self) -> Result<String, CodeGenError> {
        for function in self.ir_module.functions.iter() {
            self.generate_fun(function)?;
        }
        Ok(self.llvm_module.to_string())
    }

    fn generate_fun(&mut self, function: &'m Function) -> Result<(), CodeGenError> {
        let fn_type = self.make_fun_type(function);
        let fun = self.llvm_module.add_function(
            resolve_string_id(function.signature.name).expect("function name"),
            fn_type,
            None,
        );
        Self::setup_fun_arg(function, fun)?;

        self.build(function, fun)?;

        if !fun.verify(true) {
            panic!("Invalid function");
        }

        Ok(())
    }

    fn build(
        &mut self,
        function: &'m Function,
        fun: FunctionValue<'c>,
    ) -> Result<(), CodeGenError> {
        let bb = self.context.append_basic_block(fun, "entry");
        self.builder.position_at_end(bb);

        let fun_ctx = FunctionContext::new(function.body);
        fun_ctx.alloca_variables(function.body, self.context, &self.builder)?;

        for instruction in function.body.instructions.borrow().iter() {
            match &instruction.payload {
                InstructionPayload::Constant { constant, .. } => {
                    self.handle_constant(&fun_ctx, instruction.id, constant);
                }
                InstructionPayload::Unary {
                    operand_type,
                    operator,
                    operand,
                } => {
                    self.handle_unary(&fun_ctx, instruction.id, operand_type, operator, *operand)?;
                }
                InstructionPayload::Binary {
                    operand_type,
                    operator,
                    left,
                    right,
                } => {
                    self.handle_binary(
                        &fun_ctx,
                        instruction.id,
                        operand_type,
                        operator,
                        *left,
                        *right,
                    )?;
                }
                InstructionPayload::Ret => {
                    self.builder.build_return(None)?;
                }
                InstructionPayload::RetExpr {
                    expression,
                    operand_type,
                } => {
                    self.handle_return_expression(&fun_ctx, *expression, operand_type)?;
                }
                InstructionPayload::Load {
                    operand_type,
                    symbol_kind,
                    ..
                } => Self::handle_load(fun, &fun_ctx, instruction, operand_type, *symbol_kind),
                InstructionPayload::Let {
                    variable_index,
                    operand_type,
                    initializer,
                    ..
                } => self.handle_let(&fun_ctx, *variable_index, operand_type, *initializer)?,
            }
        }
        Ok(())
    }

    fn handle_load(
        fun: FunctionValue<'c>,
        fun_ctx: &FunctionContext<'c>,
        instruction: &Instruction,
        operand_type: &Type,
        symbol_kind: SymbolKind,
    ) {
        match symbol_kind {
            SymbolKind::Function => todo!(),
            SymbolKind::Variable => todo!(),
            SymbolKind::Argument { index } => {
                let value = fun
                    .get_nth_param(index.into())
                    .expect("valid argument number");
                match operand_type {
                    Type::Int => {
                        fun_ctx.int_values.borrow_mut()[instruction.id.as_usize()] =
                            Some(value.into_int_value());
                    }
                    Type::Boolean => {
                        fun_ctx.bool_values.borrow_mut()[instruction.id.as_usize()] =
                            Some(value.into_int_value());
                    }
                    Type::Double => {
                        todo!()
                    }
                }
            }
        }
    }

    fn handle_let(
        &self,
        fun_ctx: &FunctionContext<'c>,
        variable_index: VariableIndex,
        operand_type: &Type,
        initializer: InstructionId,
    ) -> Result<(), CodeGenError> {
        let variable_index: usize = variable_index.into();
        let var_pointer = *fun_ctx
            .int_bool_variable
            .borrow()
            .get(variable_index)
            .expect("variable index should be valid");

        let initializer = match operand_type {
            Type::Int => fun_ctx
                .int_values
                .borrow()
                .get(initializer.as_usize())
                .expect("vector should be initialized with the correct length")
                .expect("let initializer should be an int"),
            Type::Boolean => fun_ctx
                .bool_values
                .borrow()
                .get(initializer.as_usize())
                .expect("vector should be initialized with the correct length")
                .expect("let initializer should be a bool"),
            Type::Double => todo!(),
        };

        self.builder.build_store(var_pointer, initializer)?;
        Ok(())
    }

    fn make_fun_type(&mut self, function: &Function) -> FunctionType<'c> {
        let arguments = function
            .signature
            .arguments
            .iter()
            .map(|arg| match arg.argument_type {
                Type::Int => self.context.i64_type().into(),
                Type::Boolean => self.context.bool_type().into(),
                Type::Double => self.context.f64_type().into(),
            })
            .collect::<Vec<_>>();

        match &function.signature.return_type {
            None => self.context.void_type().fn_type(&arguments, false),
            Some(t) => match t {
                Type::Int => self.context.i64_type().fn_type(&arguments, false),
                Type::Boolean => self.context.bool_type().fn_type(&arguments, false),
                Type::Double => self.context.f64_type().fn_type(&arguments, false),
            },
        }
    }

    fn setup_fun_arg(function: &Function, fun: FunctionValue<'c>) -> Result<(), CodeGenError> {
        for (i, arg) in function.signature.arguments.iter().enumerate() {
            let arg_value = fun.get_nth_param(i as u32).expect("should have argument");
            arg_value.set_name(resolve_string_id(arg.name).expect("function argument name"));
        }
        Ok(())
    }

    fn handle_binary(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        operand_type: &Type,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_binary_int(fun_ctx, id, operator, left, right)?;
            }

            Type::Boolean => {
                self.handle_binary_boolean(fun_ctx, id, operator, left, right)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn handle_binary_boolean(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = fun_ctx
            .bool_values
            .borrow()
            .get(left.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be a bool");
        let right = fun_ctx
            .bool_values
            .borrow()
            .get(right.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be a bool");

        fun_ctx.bool_values.borrow_mut()[id.as_usize()] = Some(match operator {
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
        });
        Ok(())
    }

    fn handle_binary_int(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = fun_ctx
            .int_values
            .borrow()
            .get(left.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be an int");
        let right = fun_ctx
            .int_values
            .borrow()
            .get(right.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be an int");

        fun_ctx.int_values.borrow_mut()[id.as_usize()] = Some(match operator {
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
                // TODO
                unreachable!()
            }
        });
        Ok(())
    }

    fn handle_unary(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        operand_type: &Type,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_unary_int(fun_ctx, id, operator, operand)?;
            }
            Type::Boolean => {
                self.handle_unary_boolean(fun_ctx, id, operator, operand)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn name(prefix: &str, id: InstructionId) -> String {
        format!("{}_{}", prefix, id)
    }

    fn handle_unary_boolean(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = fun_ctx
            .bool_values
            .borrow()
            .get(operand.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("unary operand should be a bool");
        fun_ctx.bool_values.borrow_mut()[id.as_usize()] = Some(match operator {
            UnaryOperator::Neg | UnaryOperator::BitwiseNot => {
                unreachable!()
            }
            UnaryOperator::Not => self.builder.build_not(operand, &Self::name("not", id))?,
        });
        Ok(())
    }

    fn handle_unary_int(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = fun_ctx
            .int_values
            .borrow()
            .get(operand.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("unary operand should be an int");
        fun_ctx.int_values.borrow_mut()[id.as_usize()] = Some(match operator {
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
                // TODO: error
                unreachable!("unexpected not operator with int type")
            }
        });
        Ok(())
    }

    fn handle_constant(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        id: InstructionId,
        constant: &LiteralValue,
    ) {
        match constant {
            LiteralValue::Integer(value) => {
                let mut int_values_borrow = fun_ctx.int_values.borrow_mut();
                let option = int_values_borrow
                    .get_mut(id.as_usize())
                    .expect("vector should be initialized with the correct length");
                *option = Some(self.context.i64_type().const_int(*value as u64, false));
            }
            LiteralValue::Boolean(value) => {
                let mut bool_values_borrow = fun_ctx.bool_values.borrow_mut();
                let option = bool_values_borrow
                    .get_mut(id.as_usize())
                    .expect("vector should be initialized with the correct length");
                *option = Some(
                    self.context
                        .bool_type()
                        .const_int(if *value { 1 } else { 0 }, false),
                );
            }
            LiteralValue::Double(..) => todo!(),
        };
    }

    fn handle_return_expression(
        &mut self,
        fun_ctx: &FunctionContext<'c>,
        expression: InstructionId,
        operand_type: &Type,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                let operand = fun_ctx
                    .int_values
                    .borrow()
                    .get(expression.as_usize())
                    .expect("vector should be initialized with the correct length")
                    .expect("return expression should be an int");
                self.builder.build_return(Some(&operand))?;
            }
            Type::Boolean => {
                let operand = fun_ctx
                    .bool_values
                    .borrow()
                    .get(expression.as_usize())
                    .expect("vector should be initialized with the correct length")
                    .expect("return expression should be a bool");
                self.builder.build_return(Some(&operand))?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }
}

#[allow(unused)]
fn ir_to_llvm(context: &Context, module: &codegen::Module) -> Result<String, CodeGenError> {
    let mut builder = LlvmGenerator::new(context, module);
    builder.generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::build_ir_module;
    use codegen::IrAllocator;
    use inkwell::context::Context;
    use semantic_analysis::{SemanticAnalyzer, TypedModule};
    use std::io::{stderr, Write};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'s>(
        semantic_analyzer: &'s SemanticAnalyzer,
        source: &str,
    ) -> &'s TypedModule<'s> {
        let ast_allocator = parser::AstAllocator::default();
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

    #[test]
    fn test_ir_to_llvm() {
        let ir_allocator = IrAllocator::new();
        let basic_block = handle_module(
            &ir_allocator,
            r"fn empty() {
}

fn add_one(x: int) -> int {
  return 1 + x;
}

fn add(x: int, y: int) -> int {
  return x + y;
}

fn greater(x: int, y: int) -> boolean {
  return x > y;
}

fn declare_var() {
    let x = 1;
    let y = true;
}
",
        );

        let context = Context::create();
        let llvm_ir = ir_to_llvm(&context, basic_block).unwrap();

        println!("Generated LLVM IR:\n{}", llvm_ir);
        // TODO: assert something on the generated IR
    }
}
