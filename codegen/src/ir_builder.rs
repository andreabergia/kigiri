use crate::ir::{BasicBlock, Function, FunctionArgument, Instruction, IrAllocator, Module};
use crate::{FunctionSignature, ir};
use ir::Variable;
use parser::{Expression, FunctionDeclaration, Statement};
use semantic_analysis::{PhaseTypeResolved, Symbol, SymbolKind, SymbolTable, Type, VariableIndex};

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

    fn generate(&self, function: &FunctionDeclaration<PhaseTypeResolved>) -> &'i Function<'i> {
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
        function: &FunctionDeclaration<PhaseTypeResolved>,
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

                    let argument_type =
                        if let SymbolKind::Argument { argument_type, .. } = symbol.kind {
                            argument_type
                        } else {
                            panic!("expected an argument symbol kind for function argument");
                        };
                    FunctionArgument {
                        name: symbol.name,
                        argument_type,
                    }
                })),
        )
    }

    fn handle_statement(
        &self,
        statement: &Statement<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
    ) -> FoundReturn {
        match statement {
            Statement::Let { initializers } => {
                for initializer in initializers {
                    let symbol = symbol_table
                        .lookup_by_id(initializer.variable)
                        .expect("should find symbol in symbol table");
                    let value = self.handle_expression(initializer.value, symbol_table);

                    let (variable_index, variable_type) = if let SymbolKind::Variable {
                        index,
                        variable_type,
                    } = symbol.kind
                    {
                        (index, variable_type)
                    } else {
                        panic!("expected a variable symbol kind for let statement");
                    };
                    let instruction = self.ir_allocator.new_let(
                        variable_index,
                        symbol.name,
                        variable_type,
                        value.id,
                    );
                    self.push_to_current_bb(instruction);
                    self.push_variable_to_current_bb(variable_index, symbol, variable_type);
                }
                FoundReturn::No
            }
            Statement::Assignment {
                target: symbol,
                expression,
            } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol)
                    .expect("should find symbol in symbol table");
                let value = self.handle_expression(expression, symbol_table);

                let (variable_index, variable_type) = if let SymbolKind::Variable {
                    index,
                    variable_type,
                } = symbol.kind
                {
                    (index, variable_type)
                } else {
                    panic!("expected a variable symbol kind for let statement");
                };
                let instruction =
                    self.ir_allocator
                        .new_store(symbol.name, variable_type, variable_index, value);
                self.push_to_current_bb(instruction);
                FoundReturn::No
            }
            Statement::Return { expression } => {
                if let Some(value) = expression {
                    let instruction = self.handle_expression(value, symbol_table);
                    self.push_to_current_bb(self.ir_allocator.new_ret_expr(instruction));
                } else {
                    self.push_to_current_bb(self.ir_allocator.new_ret())
                }
                FoundReturn::Yes
            }
            Statement::Expression { expression } => {
                self.handle_expression(expression, symbol_table);
                FoundReturn::No
            }
            Statement::NestedBlock { .. } => todo!(),
        }
    }

    fn handle_expression(
        &self,
        expression: &Expression<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
    ) -> &'i Instruction {
        match expression {
            Expression::Identifier {
                resolved_type,
                name: symbol_id,
            } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol_id)
                    .expect("should find identifier in symbol table");

                let instruction = match symbol.kind {
                    SymbolKind::Function { .. } => todo!(),
                    SymbolKind::Variable {
                        index,
                        variable_type,
                    } => self
                        .ir_allocator
                        .new_load_var(symbol.name, variable_type, index),
                    SymbolKind::Argument {
                        index,
                        argument_type,
                    } => self
                        .ir_allocator
                        .new_load_arg(symbol.name, argument_type, index),
                };

                self.push_to_current_bb(instruction);
                instruction
            }
            Expression::Literal {
                resolved_type,
                value,
            } => {
                let instruction = self.ir_allocator.new_const(value.clone());
                self.push_to_current_bb(instruction);
                instruction
            }
            Expression::Unary {
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
            Expression::Binary {
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
            Expression::FunctionCall { .. } => todo!(),
        }
    }

    fn push_to_current_bb(&self, instruction: &'i Instruction) {
        self.current_bb.instructions.borrow_mut().push(instruction);
    }

    fn push_variable_to_current_bb(
        &self,
        variable_index: VariableIndex,
        symbol: &Symbol,
        variable_type: Type,
    ) {
        self.current_bb.variables.borrow_mut().push(Variable {
            index: variable_index,
            name: symbol.name,
            variable_type,
        });
    }
}

pub fn build_ir_module<'i>(
    ir_allocator: &'i IrAllocator,
    module: &parser::Module<PhaseTypeResolved>,
) -> &'i Module<'i> {
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

    fn analyze_module<'i>(ir_allocator: &'i IrAllocator, source: &str) -> &'i Module<'i> {
        let ast_allocator = parser::ParsedAstAllocator::default();
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
        fn_unary,
        r"fn neg(x: int) -> int {
    return - x;
}",
        r"module test

fn neg(
  x: int,
) -> i
{ #0
  00000 i loadarg x
  00001 i neg @0
  00002 i ret @1
}
"
    );

    test_module_ir!(
        fn_binary,
        r"fn add_one(x: double) -> double {
    return 1.0 + x;
}",
        r"module test

fn add_one(
  x: double,
) -> d
{ #0
  00000 d const 1d
  00001 d loadarg x
  00002 d add @0, @1
  00003 d ret @2
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
        r"fn var() -> boolean {
    let y = true;
    return y;
}",
        r"module test

fn var(
) -> b
{ #0
  var y: boolean
  00000 b const true
  00001 b let y = @0
  00002 b loadvar y
  00003 b ret @2
}
"
    );
    test_module_ir!(
        multiple_variable_declaration,
        r"fn var() { 
    let y = 1, z = 2;
}",
        r"module test

fn var(
) -> void
{ #0
  var y: int
  var z: int
  00000 i const 1i
  00001 i let y = @0
  00002 i const 2i
  00003 i let z = @2
  00004 v ret
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
  00003 i storevar y = @2
  00004 i loadvar y
  00005 i ret @4
}
"
    );
    test_module_ir!(
        argument_reassignment,
        r"fn arg_assign(x: int) -> int {
    x = x + 1;
    return x;
}",
        r"module test

fn arg_assign(
  x: int,
) -> i
{ #0
  var x: int
  00000 i loadarg x
  00001 i const 1i
  00002 i add @0, @1
  00003 i let x = @2
  00004 i loadvar x
  00005 i ret @4
}
"
    );
}
