use crate::ir::*;
use semantic_analysis::TypedExpression;
use std::cell::RefCell;

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
            TypedExpression::Identifier { .. } => {
                todo!()
            }
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

                let name = self.instr_name(operator.name());
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

                let name = self.instr_name(operator.name());
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
}

pub fn build_ir<'ir>(ir: &'ir Ir, expression: &TypedExpression) -> &'ir BasicBlock<'ir> {
    let builder = IrBuilder::new(ir);
    builder.generate(expression);
    builder.first_bb
}

#[cfg(test)]
mod tests {
    use super::*;
    use semantic_analysis::SemanticAnalyzer;

    fn make_analyzed_ast<'te>(
        semantic_analyzer: &'te SemanticAnalyzer,
        source: &str,
    ) -> &'te TypedExpression<'te> {
        let ast = parser::Ast::default();
        let expression = parser::parse_as_expression(&ast, source);
        let symbol_table = semantic_analyzer.symbol_table(None);

        let result = semantic_analyzer.analyze_expression(expression, symbol_table);
        result.expect("should have passed semantic analysis")
    }

    fn basic_block_from_source<'ir>(ir: &'ir Ir, source: &str) -> &'ir BasicBlock<'ir> {
        let semantic_analysis = SemanticAnalyzer::default();
        let expression = make_analyzed_ast(&semantic_analysis, source);
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

    test_ir!(const_int, "1", "0_const         i = const(1i)\n");
    test_ir!(const_dbl, "2.0", "0_const         d = const(2d)\n");
    test_ir!(const_bool, "true", "0_const         b = const(true)\n");

    test_ir!(
        neg_int,
        "- 3",
        "0_const         i = const(3i)\n\
        1_neg           i = neg(0_const)\n"
    );

    test_ir!(
        add_int,
        "1 + 2",
        "0_const         i = const(1i)\n\
        1_const         i = const(2i)\n\
        2_add           i = add(0_const, 1_const)\n"
    );

    test_ir!(
        mixed_expression,
        "1 + 2 * 3 < 4",
        "0_const         i = const(1i)\n\
        1_const         i = const(2i)\n\
        2_const         i = const(3i)\n\
        3_mul           i = mul(1_const, 2_const)\n\
        4_add           i = add(0_const, 3_mul)\n\
        5_const         i = const(4i)\n\
        6_lt            i = lt(4_add, 5_const)\n"
    );
}
