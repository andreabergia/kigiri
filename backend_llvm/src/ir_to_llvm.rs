use codegen::{InstructionId, InstructionPayload, LiteralValue};
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::FunctionType;
use inkwell::values::IntValue;
use inkwell::IntPredicate;
use parser::{resolve_string_id, BinaryOperator, UnaryOperator};
use semantic_analysis::Type;
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
    int_values: Vec<Option<IntValue<'c>>>,
    bool_values: Vec<Option<IntValue<'c>>>,
}

impl FunctionContext<'_> {
    fn new(num_instructions: usize) -> Self {
        let mut int_values = Vec::with_capacity(num_instructions);
        int_values.resize(num_instructions, None);

        let mut bool_values = Vec::with_capacity(num_instructions);
        bool_values.resize(num_instructions, None);

        Self {
            int_values,
            bool_values,
        }
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

    fn generate(&mut self) -> Result<(), CodeGenError> {
        for function in self.ir_module.functions.iter() {
            self.generate_fun(function)?;
        }
        Ok(())
    }

    fn generate_fun(&mut self, function: &codegen::Function) -> Result<(), CodeGenError> {
        let mut fun_ctx = FunctionContext::new(function.body.instructions.borrow().len());

        let fn_type = self.make_fun_type(function);
        let fun = self.llvm_module.add_function(
            resolve_string_id(function.signature.name).expect("function name"),
            fn_type,
            None,
        );

        let bb = self.context.append_basic_block(fun, "entry");
        self.builder.position_at_end(bb);

        for instruction in function.body.instructions.borrow().iter() {
            match &instruction.payload {
                InstructionPayload::Constant { constant, .. } => {
                    self.handle_constant(&mut fun_ctx, instruction.id, constant);
                }

                InstructionPayload::Unary {
                    operand_type,
                    operator,
                    operand,
                } => {
                    self.handle_unary(
                        &mut fun_ctx,
                        instruction.id,
                        operand_type,
                        operator,
                        *operand,
                    )?;
                }
                InstructionPayload::Binary {
                    operand_type,
                    operator,
                    left,
                    right,
                } => {
                    self.handle_binary(
                        &mut fun_ctx,
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
                &InstructionPayload::RetExpr { .. } => todo!(),
                &InstructionPayload::Load { .. } => todo!(),
            }
        }

        if !fun.verify(true) {
            panic!("Invalid function");
        }

        fun.print_to_stderr();
        Ok(())
    }

    fn make_fun_type(&mut self, function: &codegen::Function) -> FunctionType<'c> {
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

    fn handle_binary(
        &mut self,
        fun_ctx: &mut FunctionContext<'c>,
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
        fun_ctx: &mut FunctionContext<'c>,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = fun_ctx
            .bool_values
            .get(left.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be a bool");
        let right = fun_ctx
            .bool_values
            .get(right.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be a bool");

        fun_ctx.bool_values[id.as_usize()] = Some(match operator {
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
        fun_ctx: &mut FunctionContext<'c>,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = fun_ctx
            .int_values
            .get(left.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be an int");
        let right = fun_ctx
            .int_values
            .get(right.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be an int");

        fun_ctx.int_values[id.as_usize()] = Some(match operator {
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
        fun_ctx: &mut FunctionContext<'c>,
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
        fun_ctx: &mut FunctionContext<'c>,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = fun_ctx
            .bool_values
            .get(operand.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("unary operand should be a bool");
        fun_ctx.bool_values[id.as_usize()] = Some(match operator {
            UnaryOperator::Neg | UnaryOperator::BitwiseNot => {
                unreachable!()
            }
            UnaryOperator::Not => self.builder.build_not(operand, &Self::name("not", id))?,
        });
        Ok(())
    }

    fn handle_unary_int(
        &mut self,
        fun_ctx: &mut FunctionContext<'c>,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = fun_ctx
            .int_values
            .get(operand.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("unary operand should be an int");
        fun_ctx.int_values[id.as_usize()] = Some(match operator {
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
        fun_ctx: &mut FunctionContext<'c>,
        id: InstructionId,
        constant: &LiteralValue,
    ) {
        match constant {
            LiteralValue::Integer(value) => {
                let option = fun_ctx
                    .int_values
                    .get_mut(id.as_usize())
                    .expect("vector should be initialized with the correct length");
                *option = Some(self.context.i64_type().const_int(*value as u64, false));
            }
            LiteralValue::Boolean(value) => {
                let option = fun_ctx
                    .bool_values
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
}

#[allow(unused)]
fn ir_to_llvm(context: &Context, module: &codegen::Module) -> Result<(), CodeGenError> {
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
            r"fn simple() {
  1 + 2;
}
",
            // fn add_one(x: int) -> int {
            //     return 1;
            // }
            // ",
        );

        let context = Context::create();
        ir_to_llvm(&context, basic_block).unwrap();
    }
}
