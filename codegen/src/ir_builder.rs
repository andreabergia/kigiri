use crate::ir::*;
use parser::{BinaryOperator, UnaryOperator};
use std::cell::RefCell;
use type_engine::TypedExpression;

#[derive(Default, Debug)]
struct Counter {
    value: i32,
}

impl Counter {
    fn increment(&mut self) -> i32 {
        let old = self.value;
        self.value += 1;
        old
    }
}

struct IrBuilder<'ir> {
    name_counter: RefCell<Counter>,
    ir: &'ir Ir,
    pub(crate) first_bb: &'ir BasicBlock<'ir>,
    current_bb: &'ir BasicBlock<'ir>,
}

impl<'ir> IrBuilder<'ir> {
    fn new(ir: &'ir Ir) -> Self {
        let basic_block = ir.basic_block();
        Self {
            name_counter: RefCell::default(),
            ir,
            first_bb: basic_block,
            current_bb: basic_block,
        }
    }

    fn generate(&self, expression: &TypedExpression) -> &'ir Instruction<'ir> {
        match expression {
            TypedExpression::Literal {
                resolved_type,
                value,
            } => {
                let name = self.instr_name("const");
                let instruction = self.ir.new_const(&name, value.clone());
                self.push_to_current_bb(instruction);
                instruction
            }
            TypedExpression::Unary {
                resolved_type,
                operator,
                operand,
            } => {
                let operand_instruction = self.generate(operand);

                let name = self.instr_name(Self::instruction_name_for_unary(operator));
                let instruction = self
                    .ir
                    .new_unary(&name, operator.clone(), operand_instruction);
                self.push_to_current_bb(instruction);
                instruction
            }
            TypedExpression::Binary {
                resolved_type,
                operator,
                left,
                right,
            } => {
                let left_instruction = self.generate(left);
                let right_instruction = self.generate(right);

                let name = self.instr_name(Self::instruction_name_for_binary(operator));
                let instruction = self.ir.new_binary(
                    &name,
                    operator.clone(),
                    left_instruction,
                    right_instruction,
                );
                self.push_to_current_bb(instruction);
                instruction
            }
        }
    }

    fn instr_name(&self, suffix: &str) -> String {
        format!("{}_{}", self.name_counter.borrow_mut().increment(), suffix)
    }

    fn push_to_current_bb(&self, instruction: &'ir Instruction<'ir>) {
        self.current_bb.instructions.borrow_mut().push(instruction);
    }

    fn instruction_name_for_unary(operator: &UnaryOperator) -> &'static str {
        match operator {
            UnaryOperator::Neg => "neg",
            UnaryOperator::Not => "not",
            UnaryOperator::BitwiseNot => "bitwise_not",
        }
    }

    fn instruction_name_for_binary(operator: &BinaryOperator) -> &'static str {
        match operator {
            BinaryOperator::Add => "add",
            BinaryOperator::Sub => "sub",
            BinaryOperator::Mul => "mul",
            BinaryOperator::Div => "div",
            BinaryOperator::Rem => "rem",
            BinaryOperator::Exp => "exp",
            BinaryOperator::Eq => "eq",
            BinaryOperator::Neq => "neq",
            BinaryOperator::Lt => "lt",
            BinaryOperator::Lte => "lte",
            BinaryOperator::Gt => "gt",
            BinaryOperator::Gte => "gte",
            BinaryOperator::And => "and",
            BinaryOperator::Or => "or",
            BinaryOperator::BitwiseAnd => "bitwise_and",
            BinaryOperator::BitwiseOr => "bitwise_or",
            BinaryOperator::BitwiseXor => "bitwise_xor",
            BinaryOperator::BitwiseShl => "bitwise_shl",
            BinaryOperator::BitwiseShr => "bitwise_shr",
        }
    }
}

pub fn build_ir<'ir>(ir: &'ir Ir, expression: &TypedExpression) -> &'ir BasicBlock<'ir> {
    let builder = IrBuilder::new(ir);
    builder.generate(expression);
    builder.first_bb
}

#[cfg(test)]
mod tests {
    use super::*;
    use type_engine::TypeEngine;

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
        build_ir(ir, expression)
    }

    macro_rules! test_ir {
        ($name: ident, $source: expr, $expected: expr) => {
            #[test]
            fn $name() {
                let ir = Ir::new();
                let bb = basic_block_from_source(&ir, $source);
                assert_eq!(bb.to_string(), $expected);
            }
        };
    }

    test_ir!(const_int, "1", "i 0_const      = const(1i)\n");
    test_ir!(const_dbl, "2.0", "d 0_const      = const(2d)\n");
    test_ir!(const_bool, "true", "b 0_const      = const(true)\n");

    test_ir!(
        neg_int,
        "- 3",
        "i 0_const      = const(3i)\n\
        i 1_neg        = neg(0_const)\n"
    );

    test_ir!(
        add_int,
        "1 + 2",
        "i 0_const      = const(1i)\n\
        i 1_const      = const(2i)\n\
        i 2_add        = add(0_const, 1_const)\n"
    );
}
