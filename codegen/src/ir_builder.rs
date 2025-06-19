use crate::ir::{BasicBlock, Function, FunctionArgument, Instruction, IrAllocator, Module};
use semantic_analysis::{
    SymbolTable, TypedExpression, TypedFunctionDeclaration, TypedModule, TypedStatement,
};

struct FunctionIrBuilder<'i> {
    ir_allocator: &'i IrAllocator,
    pub(crate) first_bb: &'i BasicBlock<'i>,
    current_bb: &'i BasicBlock<'i>,
}

impl<'i> FunctionIrBuilder<'i> {
    fn new(ir_allocator: &'i IrAllocator) -> Self {
        ir_allocator.reset_instruction_id();
        let basic_block = ir_allocator.basic_block();
        Self {
            ir_allocator,
            first_bb: basic_block,
            current_bb: basic_block,
        }
    }

    fn generate(&self, function: &TypedFunctionDeclaration) -> &'i Function<'i> {
        let first_bb = self.first_bb;

        for statement in function.body.statements.iter() {
            self.handle_statement(statement, function.symbol_table);
        }

        let signature = self.ir_allocator.function_signature(
            function.signature.name,
            function.signature.return_type.clone(),
            self.ir_allocator
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

        self.ir_allocator.function(signature, first_bb)
    }

    fn handle_statement(&self, statement: &TypedStatement, symbol_table: &SymbolTable) {
        match statement {
            TypedStatement::Let { .. } => todo!(),
            TypedStatement::Assignment { .. } => todo!(),
            TypedStatement::Return { value } => {
                if let Some(value) = value {
                    let instruction = self.handle_expression(value, symbol_table);
                    self.push_to_current_bb(self.ir_allocator.new_ret_expr(instruction));
                } else {
                    self.push_to_current_bb(self.ir_allocator.new_ret())
                }
            }
            TypedStatement::Expression { expression } => {
                self.handle_expression(expression, symbol_table);
            }
            TypedStatement::NestedBlock { .. } => todo!(),
        }
    }

    fn handle_expression(
        &self,
        expression: &TypedExpression,
        symbol_table: &SymbolTable,
    ) -> &'i Instruction {
        match expression {
            TypedExpression::Identifier {
                resolved_type,
                symbol_id,
            } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol_id)
                    .expect("should find identifier in symbol table");

                let instruction = self.ir_allocator.new_load(symbol);

                self.push_to_current_bb(instruction);
                instruction
            }
            TypedExpression::Literal {
                resolved_type,
                value,
            } => {
                let instruction = self.ir_allocator.new_const(value.clone());
                self.push_to_current_bb(instruction);
                instruction
            }
            TypedExpression::Unary {
                resolved_type,
                operator,
                operand,
            } => {
                let operand_instruction = self.handle_expression(operand, symbol_table);

                let instruction = self
                    .ir_allocator
                    .new_unary(operator.clone(), operand_instruction);
                self.push_to_current_bb(instruction);
                instruction
            }
            TypedExpression::Binary {
                resolved_type,
                operator,
                left,
                right,
            } => {
                let left_instruction = self.handle_expression(left, symbol_table);
                let right_instruction = self.handle_expression(right, symbol_table);

                let instruction = self.ir_allocator.new_binary(
                    operator.clone(),
                    left_instruction,
                    right_instruction,
                );
                self.push_to_current_bb(instruction);
                instruction
            }
        }
    }

    fn push_to_current_bb(&self, instruction: &'i Instruction) {
        self.current_bb.instructions.borrow_mut().push(instruction);
    }
}

fn build_ir_expression<'i>(
    ir_allocator: &'i IrAllocator,
    expression: &TypedExpression,
    symbol_table: &SymbolTable,
) -> &'i BasicBlock<'i> {
    let builder = FunctionIrBuilder::new(ir_allocator);
    builder.handle_expression(expression, symbol_table);
    builder.first_bb
}

pub fn build_ir_module<'i>(ir_allocator: &'i IrAllocator, module: &TypedModule) -> &'i Module<'i> {
    let mut functions = ir_allocator.functions();
    for function in &module.functions {
        let fn_builder = FunctionIrBuilder::new(ir_allocator);
        functions.push(fn_builder.generate(function));
    }
    ir_allocator.module(module.name, functions)
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
            let ast_allocator = parser::AstAllocator::default();
            let expression = parser::parse_as_expression(&ast_allocator, source);
            let symbol_table = semantic_analyzer.symbol_table(None);

            let result = semantic_analyzer.analyze_expression(expression, symbol_table);
            result.expect("should have passed semantic analysis")
        }

        fn basic_block_from_expression<'i>(
            ir_allocator: &'i IrAllocator,
            source: &str,
        ) -> &'i BasicBlock<'i> {
            let semantic_analyzer = SemanticAnalyzer::default();
            let expression = analyze_expression(&semantic_analyzer, source);
            build_ir_expression(
                ir_allocator,
                expression,
                semantic_analyzer.symbol_table(None),
            )
        }

        macro_rules! test_expression_ir {
            ($name: ident, $source: expr, $expected: expr) => {
                #[test]
                fn $name() {
                    let ir_allocator = IrAllocator::new();
                    let bb = basic_block_from_expression(&ir_allocator, $source);
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

        fn analyze_module<'i>(ir_allocator: &'i IrAllocator, source: &str) -> &'i Module<'i> {
            let ast_allocator = parser::AstAllocator::default();
            let ast_module = parser::parse(&ast_allocator, "test", source);

            let semantic_analyzer = SemanticAnalyzer::default();
            let typed_module = semantic_analyzer
                .analyze_module(ast_module)
                .expect("should have passed semantic analysis");

            build_ir_module(ir_allocator, typed_module)
        }

        macro_rules! test_module_ir {
            ($name: ident, $source: expr, $expected: expr) => {
                #[test]
                fn $name() {
                    let ir_allocator = IrAllocator::new();
                    let module = analyze_module(&ir_allocator, $source);
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
        test_module_ir!(
            fn_plus_one,
            r"fn add_one(x: int) -> int {
    return 1 + x;
}",
            r"module test

fn add_one(
  x: int,
) -> i
{ #0
  00000 i const 1i
  00001 i load x
  00002 i add @0, @1
  00003 i ret @2
}
"
        );

        test_module_ir!(
            multiple_fn_reset_ir_counter,
            r"fn one() -> int { return 1; }
fn two() -> int { return 2; }",
            r"module test

fn one(
) -> i
{ #0
  00000 i const 1i
  00001 i ret @0
}
fn two(
) -> i
{ #1
  00000 i const 2i
  00001 i ret @0
}
"
        );
    }
}
