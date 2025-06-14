use crate::ir::{BasicBlock, Function, FunctionArgument, Instruction, Ir, Module};
use semantic_analysis::{TypedExpression, TypedFunctionDeclaration, TypedModule, TypedStatement};

struct FunctionIrBuilder<'ir> {
    ir: &'ir Ir,
    pub(crate) first_bb: &'ir BasicBlock<'ir>,
    current_bb: &'ir BasicBlock<'ir>,
}

impl<'ir> FunctionIrBuilder<'ir> {
    fn new(ir: &'ir Ir) -> Self {
        let basic_block = ir.basic_block();
        Self {
            ir,
            first_bb: basic_block,
            current_bb: basic_block,
        }
    }

    fn generate(&self, function: &TypedFunctionDeclaration) -> &'ir Function<'ir> {
        let first_bb = self.first_bb;

        for statement in function.body.statements.iter() {
            self.handle_statement(statement);
        }

        let signature = self.ir.function_signature(
            function.signature.name,
            function.signature.return_type.clone(),
            self.ir
                .function_arguments(function.signature.arguments.iter().map(|arg| {
                    let symbol = function
                        .symbol_table
                        .lookup_by_id(*arg)
                        .expect("should find function argument in symbol table");
                    FunctionArgument {
                        name: symbol.name,
                        argument_type: symbol.symbol_type.clone(),
                    }
                })),
        );

        self.ir.function(signature, first_bb)
    }

    fn handle_statement(&self, statement: &TypedStatement) {
        match statement {
            TypedStatement::Let { .. } => todo!(),
            TypedStatement::Assignment { .. } => todo!(),
            TypedStatement::Return { value } => {
                if let Some(value) = value {
                    let instruction = self.handle_expression(value);
                    self.push_to_current_bb(self.ir.new_ret_expr(instruction));
                } else {
                    self.push_to_current_bb(self.ir.new_ret())
                }
            }
            TypedStatement::Expression { expression } => {
                self.handle_expression(expression);
            }
            TypedStatement::NestedBlock { .. } => todo!(),
        }
    }

    fn handle_expression(&self, expression: &TypedExpression) -> &'ir Instruction {
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
                let operand_instruction = self.handle_expression(operand);

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
                let left_instruction = self.handle_expression(left);
                let right_instruction = self.handle_expression(right);

                let instruction =
                    self.ir
                        .new_binary(operator.clone(), left_instruction, right_instruction);
                self.push_to_current_bb(instruction);
                instruction
            }
        }
    }

    fn push_to_current_bb(&self, instruction: &'ir Instruction) {
        self.current_bb.instructions.borrow_mut().push(instruction);
    }
}

pub fn build_ir_expression<'ir>(ir: &'ir Ir, expression: &TypedExpression) -> &'ir BasicBlock<'ir> {
    let builder = FunctionIrBuilder::new(ir);
    builder.handle_expression(expression);
    builder.first_bb
}

fn build_ir_module<'ir>(ir: &'ir Ir, module: &TypedModule) -> &'ir Module<'ir> {
    let mut functions = ir.functions();
    for function in &module.functions {
        let fn_builder = FunctionIrBuilder::new(ir);
        functions.push(fn_builder.generate(function));
    }
    ir.module(module.name, functions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use semantic_analysis::SemanticAnalyzer;

    mod expressions {
        use super::*;

        fn analyze_expression<'s>(
            semantic_analyzer: &'s SemanticAnalyzer,
            source: &str,
        ) -> &'s TypedExpression<'s> {
            let ast = parser::Ast::default();
            let expression = parser::parse_as_expression(&ast, source);
            let symbol_table = semantic_analyzer.symbol_table(None);

            let result = semantic_analyzer.analyze_expression(expression, symbol_table);
            result.expect("should have passed semantic analysis")
        }

        fn basic_block_from_expression<'ir>(ir: &'ir Ir, source: &str) -> &'ir BasicBlock<'ir> {
            let semantic_analysis = SemanticAnalyzer::default();
            let expression = analyze_expression(&semantic_analysis, source);
            build_ir_expression(ir, expression)
        }

        macro_rules! test_expression_ir {
            ($name: ident, $source: expr, $expected: expr) => {
                #[test]
                fn $name() {
                    let ir = Ir::new();
                    let bb = basic_block_from_expression(&ir, $source);
                    assert_eq!(bb.to_string(), $expected);
                }
            };
        }

        test_expression_ir!(
            const_int,
            "1",
            r"{ #0
  00000 i const 1i
}"
        );
        test_expression_ir!(
            const_dbl,
            "2.0",
            r"{ #0
  00000 d const 2d
}"
        );
        test_expression_ir!(
            const_bool,
            "true",
            r"{ #0
  00000 b const true
}"
        );

        test_expression_ir!(
            neg_int,
            "- 3",
            r"{ #0
  00000 i const 3i
  00001 i neg @0
}"
        );

        test_expression_ir!(
            add_int,
            "1 + 2",
            r"{ #0
  00000 i const 1i
  00001 i const 2i
  00002 i add @0, @1
}"
        );

        test_expression_ir!(
            mixed_expression,
            "1 + 2 * 3 < 4",
            r"{ #0
  00000 i const 1i
  00001 i const 2i
  00002 i const 3i
  00003 i mul @1, @2
  00004 i add @0, @3
  00005 i const 4i
  00006 i lt @4, @5
}"
        );
    }

    mod modules {
        use super::*;

        fn analyze_module<'ir>(ir: &'ir Ir, source: &str) -> &'ir Module<'ir> {
            let ast = parser::Ast::default();
            let ast_module = parser::parse(&ast, "test", source);

            let semantic_analyzer = SemanticAnalyzer::default();
            let typed_module = semantic_analyzer
                .analyze_module(ast_module)
                .expect("should have passed semantic analysis");

            build_ir_module(ir, typed_module)
        }

        macro_rules! test_module_ir {
            ($name: ident, $source: expr, $expected: expr) => {
                #[test]
                fn $name() {
                    let ir = Ir::new();
                    let module = analyze_module(&ir, $source);
                    assert_eq!(module.to_string(), $expected);
                }
            };
        }

        test_module_ir!(
            fn_constant,
            r"fn one() -> int {
    return 1;
}",
            r"module test

fn one(
) -> i
{ #0
  00000 i const 1i
  00001 i ret @0
}
"
        );
    }
}
