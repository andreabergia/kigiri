use crate::ir::*;
use type_engine::Type;
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

                let instruction = self.ir.instruction(
                    resolved_type.clone(),
                    &name,
                    InstructionType::Const,
                    [],
                    Some(value.clone()),
                );
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
    use parser::LiteralValue;
    use type_engine::TypeEngine;

    #[test]
    fn test_build_ir() {
        let ast = parser::Ast::for_tests();
        let expression = parser::parse(&ast, "1");

        let type_engine = TypeEngine::default();
        let result = type_engine.check_and_infer_types(expression);
        let expression = result.expect("should have passed semantic analysis");

        let ir = Ir::new();
        let bb = build_ir(&ir, expression);

        assert_eq!(
            bb.instructions.borrow()[0],
            &Instruction {
                operand_type: Type::Int,
                name: "0_const",
                instruction_type: InstructionType::Const,
                args: bumpalo::vec![in &ir.arena; ],
                constant: Some(LiteralValue::Integer(1)),
            }
        );

        assert_eq!(
            bb.instructions.borrow()[0].to_string(),
            "i 0_const    = const(1i, )",
        );
    }
}
