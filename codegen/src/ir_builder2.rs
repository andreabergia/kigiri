use crate::ir2::{BasicBlock2, Instruction2, Ir2};
use semantic_analysis::TypedExpression;

struct IrBuilder2<'ir> {
    ir: &'ir Ir2,
    pub(crate) first_bb: &'ir BasicBlock2<'ir>,
    current_bb: &'ir BasicBlock2<'ir>,
}

impl<'ir> IrBuilder2<'ir> {
    fn new(ir: &'ir Ir2) -> Self {
        let basic_block = ir.basic_block();
        Self {
            ir,
            first_bb: basic_block,
            current_bb: basic_block,
        }
    }

    fn generate(&self, expression: &TypedExpression) -> &'ir Instruction2 {
        match expression {
            TypedExpression::Identifier { .. } => {
                todo!()
            }
            TypedExpression::Literal {
                resolved_type,
                value,
            } => {
                let instruction = self.ir.new_const(value.clone());
                self.push_to_current_bb(instruction);
                instruction
            }
            TypedExpression::Unary {
                resolved_type,
                operator,
                operand,
            } => {
                let operand_instruction = self.generate(operand);

                let instruction = self.ir.new_unary(operator.clone(), operand_instruction);
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

                let instruction =
                    self.ir
                        .new_binary(operator.clone(), left_instruction, right_instruction);
                self.push_to_current_bb(instruction);
                instruction
            }
        }
    }

    fn push_to_current_bb(&self, instruction: &'ir Instruction2) {
        self.current_bb.instructions.borrow_mut().push(instruction);
    }
}

pub fn build_ir<'ir>(ir: &'ir Ir2, expression: &TypedExpression) -> &'ir BasicBlock2<'ir> {
    let builder = IrBuilder2::new(ir);
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

    fn basic_block_from_source<'ir>(ir: &'ir Ir2, source: &str) -> &'ir BasicBlock2<'ir> {
        let semantic_analysis = SemanticAnalyzer::default();
        let expression = make_analyzed_ast(&semantic_analysis, source);
        build_ir(ir, expression)
    }

    macro_rules! test_ir {
        ($name: ident, $source: expr, $expected: expr) => {
            #[test]
            fn $name() {
                let ir = Ir2::new();
                let bb = basic_block_from_source(&ir, $source);
                assert_eq!(bb.to_string(), $expected);
            }
        };
    }

    test_ir!(const_int, "1", "00000 i const 1i\n");
    test_ir!(const_dbl, "2.0", "00000 d const 2d\n");
    test_ir!(const_bool, "true", "00000 b const true\n");

    test_ir!(
        neg_int,
        "- 3",
        "00000 i const 3i\n\
        00001 i neg @0\n"
    );

    test_ir!(
        add_int,
        "1 + 2",
        "00000 i const 1i\n\
        00001 i const 2i\n\
        00002 i add @0, @1\n"
    );

    test_ir!(
        mixed_expression,
        "1 + 2 * 3 < 4",
        "00000 i const 1i\n\
        00001 i const 2i\n\
        00002 i const 3i\n\
        00003 i mul @1, @2\n\
        00004 i add @0, @3\n\
        00005 i const 4i\n\
        00006 i lt @4, @5\n"
    );
}
