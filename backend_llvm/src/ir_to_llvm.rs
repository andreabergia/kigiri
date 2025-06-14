use codegen::{InstructionId, InstructionPayload, LiteralValue};
use inkwell::IntPredicate;
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::IntValue;
use parser::{BinaryOperator, UnaryOperator};
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

struct LlvmGenerator<'c, 'm, 'b, 'b2>
where
    'c: 'm,
{
    context: &'c Context,
    module: &'m Module<'c>,
    builder: Builder<'c>,
    ir_allocator: &'b codegen::BasicBlock<'b2>,

    // Vectors are indexed by instruction id. There's a bit of space wasted,
    // but it makes everything quite simple and fast.
    int_values: Vec<Option<IntValue<'c>>>,
    bool_values: Vec<Option<IntValue<'c>>>,
}

impl<'c, 'm, 'b, 'b2> LlvmGenerator<'c, 'm, 'b, 'b2> {
    fn new(
        context: &'c Context,
        module: &'m Module<'c>,
        ir_allocator: &'b codegen::BasicBlock<'b2>,
    ) -> Self {
        let builder = context.create_builder();
        let num_ir_instructions = ir_allocator.instructions.borrow().len();

        let mut int_values = Vec::with_capacity(num_ir_instructions);
        int_values.resize(num_ir_instructions, None);

        let mut bool_values = Vec::with_capacity(num_ir_instructions);
        bool_values.resize(num_ir_instructions, None);

        Self {
            context,
            module,
            builder,
            ir_allocator,
            int_values,
            bool_values,
        }
    }

    fn generate(&mut self) -> Result<(), CodeGenError> {
        let fn_type = self.context.void_type().fn_type(&[], false);
        let fun = self.module.add_function("test", fn_type, None);

        let bb = self.context.append_basic_block(fun, "entry");

        self.builder.position_at_end(bb);

        for instruction in self.ir_allocator.instructions.borrow().iter() {
            match &instruction.payload {
                InstructionPayload::Constant { constant, .. } => {
                    self.handle_constant(instruction.id, constant);
                }

                InstructionPayload::Unary {
                    operand_type,
                    operator,
                    operand,
                } => {
                    self.handle_unary(instruction.id, operand_type, operator, *operand)?;
                }
                InstructionPayload::Binary {
                    operand_type,
                    operator,
                    left,
                    right,
                } => {
                    self.handle_binary(instruction.id, operand_type, operator, *left, *right)?;
                }
                InstructionPayload::Ret => {
                    self.builder.build_return(None)?;
                }
                &InstructionPayload::RetExpr { .. } => todo!(),
            }
        }

        // TODO: remove
        self.builder.build_return(None)?;

        if !fun.verify(true) {
            panic!("Invalid function");
        }

        fun.print_to_stderr();
        Ok(())
    }

    fn handle_binary(
        &mut self,
        id: InstructionId,
        operand_type: &Type,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_binary_int(id, operator, left, right)?;
            }

            Type::Boolean => {
                self.handle_binary_boolean(id, operator, left, right)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn handle_binary_boolean(
        &mut self,
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self
            .bool_values
            .get(left.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be a bool");
        let right = self
            .bool_values
            .get(right.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be a bool");

        self.bool_values[id.as_usize()] = Some(match operator {
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
        id: InstructionId,
        operator: &BinaryOperator,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self
            .int_values
            .get(left.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be an int");
        let right = self
            .int_values
            .get(right.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("binary operand should be an int");

        self.int_values[id.as_usize()] = Some(match operator {
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
        id: InstructionId,
        operand_type: &Type,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_unary_int(id, operator, operand)?;
            }
            Type::Boolean => {
                self.handle_unary_boolean(id, operator, operand)?;
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
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self
            .bool_values
            .get(operand.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("unary operand should be a bool");
        self.bool_values[id.as_usize()] = Some(match operator {
            UnaryOperator::Neg | UnaryOperator::BitwiseNot => {
                unreachable!()
            }
            UnaryOperator::Not => self.builder.build_not(operand, &Self::name("not", id))?,
        });
        Ok(())
    }

    fn handle_unary_int(
        &mut self,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self
            .int_values
            .get(operand.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("unary operand should be an int");
        self.int_values[id.as_usize()] = Some(match operator {
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

    fn handle_constant(&mut self, id: InstructionId, constant: &LiteralValue) {
        match constant {
            LiteralValue::Integer(value) => {
                let option = self
                    .int_values
                    .get_mut(id.as_usize())
                    .expect("vector should be initialized with the correct length");
                *option = Some(self.context.i64_type().const_int(*value as u64, false));
            }
            LiteralValue::Boolean(value) => {
                let option = self
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
fn ir_to_llvm<'c>(
    context: &'c Context,
    module: &Module<'c>,
    ir_allocator: &codegen::BasicBlock,
) -> Result<(), CodeGenError> {
    let mut builder = LlvmGenerator::new(context, module, ir_allocator);
    builder.generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::build_ir_expression;
    use codegen::{BasicBlock, IrAllocator};
    use inkwell::context::Context;
    use semantic_analysis::{SemanticAnalyzer, TypedExpression};
    use std::io::{Write, stderr};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'te>(
        semantic_analyzer: &'te SemanticAnalyzer,
        source: &str,
    ) -> &'te TypedExpression<'te> {
        let ast_allocator = parser::AstAllocator::default();
        let expression = parser::parse_as_expression(&ast_allocator, source);
        let symbol_table = semantic_analyzer.symbol_table(None);

        let result = semantic_analyzer.analyze_expression(expression, symbol_table);
        result.expect("should have passed semantic analysis")
    }

    fn basic_block_from_source<'i>(
        ir_allocator: &'i IrAllocator,
        source: &str,
    ) -> &'i BasicBlock<'i> {
        let semantic_analyzer = SemanticAnalyzer::default();
        let expression = make_analyzed_ast(&semantic_analyzer, source);
        let bb = build_ir_expression(ir_allocator, expression);

        let bb_ir = bb
            .instructions
            .borrow()
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        eprintln!("BasicBlock IR:\n{}", bb_ir);
        stderr().flush().unwrap();

        bb
    }

    #[test]
    fn test_ir_to_llvm() {
        let ir_allocator = IrAllocator::new();
        let basic_block = basic_block_from_source(&ir_allocator, "1 + 2 * 3");

        let context = Context::create();
        let module = context.create_module("test");
        ir_to_llvm(&context, &module, basic_block).unwrap();
    }
}
