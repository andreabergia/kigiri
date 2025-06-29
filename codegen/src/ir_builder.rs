use crate::ir::{BasicBlock, Function, FunctionArgument, Instruction, IrAllocator, Module};
use crate::{FunctionSignature, ir};
use ir::Variable;
use semantic_analysis::{
    Symbol, SymbolKind, SymbolTable, TypedExpression, TypedFunctionDeclaration, TypedModule,
    TypedStatement, VariableIndex,
};

struct FunctionIrBuilder<'i> {
    ir_allocator: &'i IrAllocator,
    pub(crate) first_bb: &'i BasicBlock<'i>,
    current_bb: &'i BasicBlock<'i>,
}

#[derive(Debug, PartialEq)]
enum FoundReturn {
    Yes,
    No,
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
        let signature = self.generate_function_signature(function);

        let first_bb = self.first_bb;
        let mut found_return = false;
        for statement in function.body.statements.iter() {
            if self.handle_statement(statement, function.symbol_table) == FoundReturn::Yes {
                found_return = true;
            }
        }
        if !found_return {
            // If no return statement was found, we add an implicit return
            self.push_to_current_bb(self.ir_allocator.new_ret());
        }

        self.ir_allocator.function(signature, first_bb)
    }

    fn generate_function_signature(
        &self,
        function: &TypedFunctionDeclaration,
    ) -> &'i FunctionSignature<'i> {
        self.ir_allocator.function_signature(
            function.signature.name,
            function.signature.return_type,
            self.ir_allocator
                .function_arguments(function.signature.arguments.iter().map(|arg| {
                    let symbol = function
                        .symbol_table
                        .lookup_by_id(*arg)
                        .expect("should find function argument in symbol table");
                    FunctionArgument {
                        name: symbol.name,
                        argument_type: symbol.symbol_type,
                    }
                })),
        )
    }

    fn handle_statement(
        &self,
        statement: &TypedStatement,
        symbol_table: &SymbolTable,
    ) -> FoundReturn {
        match statement {
            TypedStatement::Let { symbol, value } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol)
                    .expect("should find symbol in symbol table");
                let initializer = self.handle_expression(value, symbol_table);

                let variable_index = if let SymbolKind::Variable { index } = symbol.kind {
                    index
                } else {
                    panic!("expected a variable symbol kind for let statement");
                };
                let instruction = self.ir_allocator.new_let(
                    variable_index,
                    symbol.name,
                    symbol.symbol_type,
                    initializer.id,
                );
                self.push_to_current_bb(instruction);
                self.push_variable_to_current_bb(variable_index, symbol);
                FoundReturn::No
            }
            TypedStatement::Assignment { symbol, value } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol)
                    .expect("should find symbol in symbol table");
                let value = self.handle_expression(value, symbol_table);

                let variable_index = if let SymbolKind::Variable { index } = symbol.kind {
                    index
                } else {
                    panic!("expected a variable symbol kind for let statement");
                };
                let instruction = self.ir_allocator.new_store(
                    symbol.name,
                    symbol.symbol_type,
                    variable_index,
                    value,
                );
                self.push_to_current_bb(instruction);
                FoundReturn::No
            }
            TypedStatement::Return { value } => {
                if let Some(value) = value {
                    let instruction = self.handle_expression(value, symbol_table);
                    self.push_to_current_bb(self.ir_allocator.new_ret_expr(instruction));
                } else {
                    self.push_to_current_bb(self.ir_allocator.new_ret())
                }
                FoundReturn::Yes
            }
            TypedStatement::Expression { expression } => {
                self.handle_expression(expression, symbol_table);
                FoundReturn::No
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
                result_type,
                operator,
                operand_type,
                left,
                right,
            } => {
                let left_instruction = self.handle_expression(left, symbol_table);
                let right_instruction = self.handle_expression(right, symbol_table);

                let instruction = self.ir_allocator.new_binary(
                    operator.clone(),
                    result_type,
                    operand_type,
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

    fn push_variable_to_current_bb(&self, variable_index: VariableIndex, symbol: &Symbol) {
        self.current_bb.variables.borrow_mut().push(Variable {
            index: variable_index,
            name: symbol.name,
            variable_type: symbol.symbol_type,
        });
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
  00006 b lt @4, @5
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
  00001 i load param x
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
        test_module_ir!(
            implicit_return_is_generated,
            "fn empty() { }",
            r"module test

fn empty(
) -> void
{ #0
  00000 v ret
}
"
        );
        test_module_ir!(
            variable_declaration,
            r"fn var() -> int { 
    let y = 1;
    return y;
}",
            r"module test

fn var(
) -> i
{ #0
  var y: int
  00000 i const 1i
  00001 i let y = @0
  00002 i load var y
  00003 i ret @2
}
"
        );
        test_module_ir!(
            variable_assignment,
            r"fn var() -> int {
    let y = 1;
    y = 2;
    return y;
}",
            r"module test

fn var(
) -> i
{ #0
  var y: int
  00000 i const 1i
  00001 i let y = @0
  00002 i const 2i
  00003 i store var y = @2
  00004 i load var y
  00005 i ret @4
}
"
        );
    }
}
