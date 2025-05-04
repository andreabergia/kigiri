use crate::ir::*;
use bumpalo::collections::Vec as BumpVec;
use parser::UnaryOperator;
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

    fn generate(&self, expression: &TypedExpression) -> BumpVec<'ir, &'ir Instruction<'ir>> {
        let mut generated = BumpVec::new_in(&self.ir.arena);

        match expression {
            TypedExpression::Literal {
                resolved_type,
                value,
            } => {
                let name = self.instr_name("const");
                let instruction = self.ir.new_const(&name, value.clone());
                self.push_to_current_bb(instruction);
                generated.push(instruction);
            }
            TypedExpression::Unary {
                resolved_type,
                operator,
                operand,
            } => {
                let operand_instructions = self.generate(operand);
                let last_instruction = operand_instructions
                    .last()
                    .expect("the operand of an unary should have generated an instruction");

                let name = self.instr_name(Self::instruction_name_for_unary(operator));
                let instruction = self.ir.new_unary(&name, operator.clone(), last_instruction);
                self.push_to_current_bb(instruction);
                generated.push(instruction);
            }
            TypedExpression::Binary { .. } => {
                todo!()
            }
        };

        generated
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
}
