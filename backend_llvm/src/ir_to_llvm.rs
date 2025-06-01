use codegen::{Instruction, InstructionPayload, LiteralValue};
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::IntValue;
use inkwell::IntPredicate;
use parser::{BinaryOperator, UnaryOperator};
use std::collections::HashMap;
use thiserror::Error;
use type_engine::Type;

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
    ir: &'b codegen::BasicBlock<'b2>,
    int_values: HashMap<&'b str, IntValue<'c>>,
    bool_values: HashMap<&'b str, IntValue<'c>>,
}

impl<'c, 'm, 'b, 'b2> LlvmGenerator<'c, 'm, 'b, 'b2> {
    fn new(context: &'c Context, module: &'m Module<'c>, ir: &'b codegen::BasicBlock<'b2>) -> Self {
        let builder = context.create_builder();
        Self {
            context,
            module,
            builder,
            ir,
            int_values: HashMap::new(),
            bool_values: HashMap::new(),
        }
    }

    fn generate(&mut self) -> Result<(), CodeGenError> {
        let fn_type = self.context.i64_type().fn_type(&[], false);
        let fun = self.module.add_function("test", fn_type, None);

        let bb = self.context.append_basic_block(fun, "entry");

        self.builder.position_at_end(bb);

        for instruction in self.ir.instructions.borrow().iter() {
            let name = instruction.name;

            match &instruction.payload {
                InstructionPayload::Constant { constant, .. } => {
                    self.handle_constant(name, constant);
                }

                InstructionPayload::Unary {
                    operand_type,
                    operator,
                    operand,
                } => {
                    self.handle_unary(name, operand_type, operator, operand)?;
                }
                InstructionPayload::Binary {
                    operand_type,
                    operator,
                    left,
                    right,
                } => {
                    self.handle_binary(name, operand_type, operator, left, right)?;
                }
                InstructionPayload::Ret => {
                    todo!()
                }
            }
        }

        let last_instr_name = self.ir.instructions.borrow().last().unwrap().name;
        let last_value = self
            .int_values
            .get(last_instr_name)
            .or(self.bool_values.get(last_instr_name))
            .unwrap();
        self.builder.build_return(Some(last_value))?;
        if !fun.verify(true) {
            panic!("Invalid function");
        }

        fun.print_to_stderr();
        Ok(())
    }

    fn handle_binary(
        &mut self,
        name: &'b str,
        operand_type: &Type,
        operator: &BinaryOperator,
        left: &Instruction,
        right: &Instruction,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_binary_int(name, operator, left, right)?;
            }

            Type::Boolean => {
                self.handle_binary_boolean(name, operator, left, right)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn handle_binary_boolean(
        &mut self,
        name: &'b str,
        operator: &BinaryOperator,
        left: &Instruction,
        right: &Instruction,
    ) -> Result<(), CodeGenError> {
        let left = *self
            .bool_values
            .get(left.name)
            .expect("binary operand should be a bool");
        let right = *self
            .bool_values
            .get(right.name)
            .expect("binary operand should be a bool");

        match operator {
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

            BinaryOperator::Eq => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::EQ, left, right, name)?,
            ),
            BinaryOperator::Neq => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::NE, left, right, name)?,
            ),
            BinaryOperator::And => self
                .bool_values
                .insert(name, self.builder.build_and(left, right, name)?),
            BinaryOperator::Or => self
                .bool_values
                .insert(name, self.builder.build_or(left, right, name)?),
        };
        Ok(())
    }

    fn handle_binary_int(
        &mut self,
        name: &'b str,
        operator: &BinaryOperator,
        left: &Instruction,
        right: &Instruction,
    ) -> Result<(), CodeGenError> {
        let left = *self
            .int_values
            .get(left.name)
            .expect("binary operand should be an int");
        let right = *self
            .int_values
            .get(right.name)
            .expect("binary operand should be an int");

        match operator {
            BinaryOperator::Add => self
                .int_values
                .insert(name, self.builder.build_int_add(left, right, name)?),
            BinaryOperator::Sub => self
                .int_values
                .insert(name, self.builder.build_int_sub(left, right, name)?),
            BinaryOperator::Mul => self
                .int_values
                .insert(name, self.builder.build_int_mul(left, right, name)?),
            BinaryOperator::Div => self
                .int_values
                .insert(name, self.builder.build_int_signed_div(left, right, name)?),
            BinaryOperator::Rem => {
                todo!()
            }
            BinaryOperator::Exp => {
                todo!()
            }
            BinaryOperator::Eq => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::EQ, left, right, name)?,
            ),
            BinaryOperator::Neq => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::NE, left, right, name)?,
            ),
            BinaryOperator::Lt => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::SLT, left, right, name)?,
            ),
            BinaryOperator::Lte => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::SLE, left, right, name)?,
            ),
            BinaryOperator::Gt => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::SGT, left, right, name)?,
            ),
            BinaryOperator::Gte => self.bool_values.insert(
                name,
                self.builder
                    .build_int_compare(IntPredicate::SGE, left, right, name)?,
            ),
            BinaryOperator::BitwiseAnd => self
                .int_values
                .insert(name, self.builder.build_and(left, right, name)?),
            BinaryOperator::BitwiseOr => self
                .int_values
                .insert(name, self.builder.build_or(left, right, name)?),
            BinaryOperator::BitwiseXor => self
                .int_values
                .insert(name, self.builder.build_xor(left, right, name)?),
            BinaryOperator::BitwiseShl => self
                .int_values
                .insert(name, self.builder.build_left_shift(left, right, name)?),
            BinaryOperator::BitwiseShr => self.int_values.insert(
                name,
                self.builder.build_right_shift(left, right, false, name)?,
            ),

            BinaryOperator::And | BinaryOperator::Or => {
                // TODO
                unreachable!()
            }
        };
        Ok(())
    }

    fn handle_unary(
        &mut self,
        name: &'b str,
        operand_type: &Type,
        operator: &UnaryOperator,
        operand: &Instruction,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_unary_int(name, operator, operand)?;
            }
            Type::Boolean => {
                self.handle_unary_boolean(name, operator, operand)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn handle_unary_boolean(
        &mut self,
        name: &'b str,
        operator: &UnaryOperator,
        operand: &Instruction,
    ) -> Result<(), CodeGenError> {
        let operand = *self
            .bool_values
            .get(operand.name)
            .expect("unary operand should be a bool");
        self.bool_values.insert(
            name,
            match operator {
                UnaryOperator::Neg | UnaryOperator::BitwiseNot => {
                    unreachable!()
                }
                UnaryOperator::Not => self.builder.build_not(operand, name)?,
            },
        );
        Ok(())
    }

    fn handle_unary_int(
        &mut self,
        name: &'b str,
        operator: &UnaryOperator,
        operand: &Instruction,
    ) -> Result<(), CodeGenError> {
        let operand = *self
            .int_values
            .get(operand.name)
            .expect("unary operand should be an int");
        self.int_values.insert(
            name,
            match operator {
                UnaryOperator::Neg => self.builder.build_int_neg(operand, name)?,
                UnaryOperator::BitwiseNot => {
                    // There's no LLVM instruction for bitwise not, but we can xor with
                    // all 1s to get the same result (i.e. complement to 1)
                    self.builder.build_xor(
                        self.context.i64_type().const_all_ones(),
                        operand,
                        name,
                    )?
                }
                UnaryOperator::Not => {
                    // TODO: error
                    unreachable!("unexpected not operator with int type")
                }
            },
        );
        Ok(())
    }

    fn handle_constant(&mut self, name: &'b str, constant: &LiteralValue) {
        match constant {
            LiteralValue::Integer(value) => {
                self.int_values.insert(
                    name,
                    self.context.i64_type().const_int(*value as u64, false),
                );
            }
            LiteralValue::Boolean(value) => {
                self.bool_values.insert(
                    name,
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
    ir: &codegen::BasicBlock,
) -> Result<(), CodeGenError> {
    let mut builder = LlvmGenerator::new(context, module, ir);
    builder.generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::Ir;
    use codegen::{build_ir, BasicBlock};
    use inkwell::context::Context;
    use std::io::{stderr, Write};
    use type_engine::{SemanticAnalyzer, TypedExpression};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'te>(
        type_engine: &'te SemanticAnalyzer,
        source: &str,
    ) -> &'te TypedExpression<'te> {
        let ast = parser::Ast::default();
        let expression = parser::parse_as_expression(&ast, source);

        let result = type_engine.analyze_expression(expression);
        result.expect("should have passed semantic analysis")
    }

    fn basic_block_from_source<'ir>(ir: &'ir Ir, source: &str) -> &'ir BasicBlock<'ir> {
        let type_engine = SemanticAnalyzer::default();
        let expression = make_analyzed_ast(&type_engine, source);
        let bb = build_ir(ir, expression);

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
        let ir = Ir::new();
        let basic_block = basic_block_from_source(&ir, "1 + 2 * 3");

        let context = Context::create();
        let module = context.create_module("test");
        ir_to_llvm(&context, &module, basic_block).unwrap();
    }
}
