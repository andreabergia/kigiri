use codegen::{InstructionPayload, LiteralValue};
use inkwell::builder::BuilderError;
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

fn ir_to_llvm<'c>(
    context: &'c Context,
    module: &Module<'c>,
    ir: &codegen::BasicBlock,
) -> Result<(), CodeGenError> {
    let builder = context.create_builder();

    let fn_type = context.i64_type().fn_type(&[], false);
    let fun = module.add_function("test", fn_type, None);

    let bb = context.append_basic_block(fun, "entry");

    builder.position_at_end(bb);

    let mut int_values: HashMap<&str, IntValue> = HashMap::new();
    let mut bool_values: HashMap<&str, IntValue> = HashMap::new();

    for instruction in ir.instructions.borrow().iter() {
        let name = instruction.name;

        match &instruction.payload {
            InstructionPayload::Constant { constant, .. } => {
                match constant {
                    LiteralValue::Integer(value) => {
                        int_values.insert(name, context.i64_type().const_int(*value as u64, false));
                    }
                    LiteralValue::Boolean(value) => {
                        bool_values.insert(
                            name,
                            context
                                .bool_type()
                                .const_int(if *value { 1 } else { 0 }, false),
                        );
                    }
                    LiteralValue::Double(..) => todo!(),
                };
            }

            InstructionPayload::Unary {
                operand_type,
                operator,
                operand,
            } => {
                match operand_type {
                    Type::Int => {
                        let operand = *int_values
                            .get(operand.name)
                            .expect("unary operand should be an int");
                        int_values.insert(
                            name,
                            match operator {
                                UnaryOperator::Neg => builder.build_int_neg(operand, name)?,
                                UnaryOperator::BitwiseNot => {
                                    // There's no LLVM instruction for bitwise not, but we can xor with
                                    // all 1s to get the same result (i.e. complement to 1)
                                    builder.build_xor(
                                        context.i64_type().const_all_ones(),
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
                    }
                    Type::Boolean => {
                        let operand = *bool_values
                            .get(operand.name)
                            .expect("unary operand should be a bool");
                        bool_values.insert(
                            name,
                            match operator {
                                UnaryOperator::Neg | UnaryOperator::BitwiseNot => unreachable!(),
                                UnaryOperator::Not => builder.build_not(operand, name)?,
                            },
                        );
                    }
                    Type::Double => todo!(),
                }
            }
            InstructionPayload::Binary {
                operand_type,
                operator,
                left,
                right,
            } => {
                match operand_type {
                    Type::Int => {
                        let left = *int_values
                            .get(left.name)
                            .expect("binary operand should be an int");
                        let right = *int_values
                            .get(right.name)
                            .expect("binary operand should be an int");

                        match operator {
                            BinaryOperator::Add => {
                                int_values.insert(name, builder.build_int_add(left, right, name)?)
                            }
                            BinaryOperator::Sub => {
                                int_values.insert(name, builder.build_int_sub(left, right, name)?)
                            }
                            BinaryOperator::Mul => {
                                int_values.insert(name, builder.build_int_mul(left, right, name)?)
                            }
                            BinaryOperator::Div => int_values
                                .insert(name, builder.build_int_signed_div(left, right, name)?),
                            BinaryOperator::Rem => {
                                todo!()
                            }
                            BinaryOperator::Exp => {
                                todo!()
                            }
                            BinaryOperator::Eq => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::EQ, left, right, name)?,
                            ),
                            BinaryOperator::Neq => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::NE, left, right, name)?,
                            ),
                            BinaryOperator::Lt => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::SLT, left, right, name)?,
                            ),
                            BinaryOperator::Lte => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::SLE, left, right, name)?,
                            ),
                            BinaryOperator::Gt => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::SGT, left, right, name)?,
                            ),
                            BinaryOperator::Gte => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::SGE, left, right, name)?,
                            ),
                            BinaryOperator::BitwiseAnd => {
                                int_values.insert(name, builder.build_and(left, right, name)?)
                            }
                            BinaryOperator::BitwiseOr => {
                                int_values.insert(name, builder.build_or(left, right, name)?)
                            }
                            BinaryOperator::BitwiseXor => {
                                int_values.insert(name, builder.build_xor(left, right, name)?)
                            }
                            BinaryOperator::BitwiseShl => int_values
                                .insert(name, builder.build_left_shift(left, right, name)?),
                            BinaryOperator::BitwiseShr => int_values
                                .insert(name, builder.build_right_shift(left, right, false, name)?),

                            BinaryOperator::And | BinaryOperator::Or => {
                                // TODO
                                unreachable!()
                            }
                        };
                    }

                    Type::Boolean => {
                        let left = *bool_values
                            .get(left.name)
                            .expect("binary operand should be a bool");
                        let right = *bool_values
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

                            BinaryOperator::Eq => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::EQ, left, right, name)?,
                            ),
                            BinaryOperator::Neq => bool_values.insert(
                                name,
                                builder.build_int_compare(IntPredicate::NE, left, right, name)?,
                            ),
                            BinaryOperator::And => {
                                bool_values.insert(name, builder.build_and(left, right, name)?)
                            }
                            BinaryOperator::Or => {
                                bool_values.insert(name, builder.build_or(left, right, name)?)
                            }
                        };
                    }
                    Type::Double => todo!(),
                }
            }
            InstructionPayload::Ret => {
                todo!()
            }
        }
    }

    let last_instr_name = ir.instructions.borrow().last().unwrap().name;
    let last_value = int_values
        .get(last_instr_name)
        .or(bool_values.get(last_instr_name))
        .unwrap();
    builder.build_return(Some(last_value))?;
    if !fun.verify(true) {
        panic!("Invalid function");
    }

    fun.print_to_stderr();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::Ir;
    use codegen::{build_ir, BasicBlock};
    use inkwell::context::Context;
    use std::io::{stderr, Write};
    use type_engine::{TypeEngine, TypedExpression};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'te>(
        type_engine: &'te TypeEngine,
        source: &str,
    ) -> &'te TypedExpression<'te> {
        let ast = parser::Ast::for_tests();
        let expression = parser::parse(&ast, source);

        let result = type_engine.check_and_infer_types(expression);
        result.expect("should have passed semantic analysis")
    }

    fn basic_block_from_source<'ir>(ir: &'ir Ir, source: &str) -> &'ir BasicBlock<'ir> {
        let type_engine = TypeEngine::default();
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
