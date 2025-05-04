use crate::ir::*;
use type_engine::TypedExpression;

struct IrBuilder<'a> {
    name_index: i32,
    ir: &'a Ir,
    pub(crate) first_bb: &'a BasicBlock<'a>,
    current_bb: &'a BasicBlock<'a>,
}

impl<'a> IrBuilder<'a> {
    fn new(ir: &'a Ir) -> Self {
        let basic_block = ir.basic_block();
        Self {
            name_index: 0,
            ir,
            first_bb: basic_block,
            current_bb: basic_block,
        }
    }

    fn generate(&mut self, expression: &TypedExpression) {
        match expression {
            TypedExpression::Literal {
                resolved_type,
                value,
            } => {
                let name = format!("{}_const", self.name_index);
                self.name_index += 1;

                let instruction = self.ir.new_const(&name, value.clone());
                self.current_bb.instructions.borrow_mut().push(instruction);
            }
            TypedExpression::Unary { .. } => {
                todo!()
            }
            TypedExpression::Binary { .. } => {
                todo!()
            }
        }
    }
}

pub fn build_ir<'ir>(ir: &'ir Ir, expression: &TypedExpression) -> &'ir BasicBlock<'ir> {
    let mut builder = IrBuilder::new(ir);
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
}
