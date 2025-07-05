use crate::type_resolver::TypeResolver;
use crate::{ArgumentIndex, PhaseTypeResolved, SymbolKind, SymbolTable, Type};
use parser::{
    AstAllocator, BinaryOperator, Block, CompilationPhase, Expression, Module, PhaseParsed,
    UnaryOperator,
};
use thiserror::Error;

// For the moment I am using _one_ error type for all the passes
// I am unsure if this is better than one error type per pass, but it is
// simpler and I can always split it later.
#[derive(Debug, Error, PartialEq)]
pub enum SemanticAnalysisError {
    #[error("cannot apply operator {operator} to type {operand_type}")]
    CannotApplyUnaryOperatorToType {
        operator: UnaryOperator,
        operand_type: String,
    },
    #[error("cannot apply operator {operator} to types {left_type} and {right_type}")]
    CannotApplyBinaryOperatorToType {
        operator: BinaryOperator,
        left_type: String,
        right_type: String,
    },
    #[error("symbol not found: \"{name}\"")]
    SymbolNotFound { name: String },
    #[error(
        "invalid assignment to \"{symbol_name}\": symbol has type {symbol_type}, but expression has type {expression_type}"
    )]
    MismatchedAssignmentType {
        symbol_name: String,
        symbol_type: Type,
        expression_type: Type,
    },
    #[error("cannot assign value to function \"{name}\"")]
    CannotAssignToFunction { name: String },
    #[error("cannot assign void value to variable \"{name}\"")]
    CannotAssignVoidValue { name: String },
    #[error("type not found: \"{type_name}\"")]
    TypeNotFound { type_name: String },
}

#[derive(Default)]
pub struct SemanticAnalyzer {
    allocator: AstAllocator,
}

impl SemanticAnalyzer {
    pub fn analyze_module<'s, 'a>(
        &'s self,
        module: &Module<PhaseParsed>,
    ) -> Result<&'a Module<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError>
    where
        's: 'a,
    {
        TypeResolver {}.analyze_module(&self.allocator, module)
    }

    pub fn analyze_expression<'s, 'a>(
        &'s self,
        expr: &Expression<PhaseParsed>,
        symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a Expression<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError>
    where
        's: 'a,
    {
        TypeResolver {}.analyze_expression(&self.allocator, expr, symbol_table)
    }

    pub fn analyze_block<'s, 'a>(
        &'s self,
        block: &Block<PhaseParsed>,
        parent_symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a Block<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError>
    where
        's: 'a,
    {
        TypeResolver {}.analyze_block(&self.allocator, block, parent_symbol_table)
    }

    pub fn symbol_table<'s, 'a>(
        &'s self,
        parent: Option<&'a SymbolTable<'a>>,
    ) -> &'a SymbolTable<'a>
    where
        's: 'a,
    {
        SymbolTable::new(&self.allocator, parent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod expressions {
        use super::*;
        use crate::to_string_with_symbol_table;

        /// Generates a test case to verify the typed AST produced by a given
        /// source expression. The typed AST is passed as its string representation.
        macro_rules! test_ok {
            ($name: ident, $source: expr, $typed_ast: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::ParsedAstAllocator::default();
                    let expression = parser::parse_as_expression(&ast_allocator, $source);
                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_expression(expression, symbol_table);
                    assert_eq!(
                        to_string_with_symbol_table(
                            result.expect("should have matched types correctly"),
                            symbol_table
                        ),
                        $typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::ParsedAstAllocator::default();
                    let expression = parser::parse_as_expression(&ast_allocator, $source);
                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_expression(expression, symbol_table);
                    assert_eq!(
                        result.expect_err("should have failed to match types"),
                        $expected_error
                    );
                }
            };
        }

        // Literals

        test_ok!(literal_int, "1", "1i");
        test_ok!(literal_double, "3.14", "3.14d");
        test_ok!(literal_boolean, "true", "true");

        // Unary

        test_ok!(unary_neg_int, "- 3", "(-i 3i)");
        test_ok!(unary_neg_double, "- 3.14", "(-d 3.14d)");
        test_ko!(
            unary_neg_boolean,
            "- false",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::Neg,
                operand_type: "boolean".to_string()
            }
        );

        test_ko!(
            unary_not_int,
            "! 3",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::Not,
                operand_type: "int".to_string()
            }
        );
        test_ko!(
            unary_not_double,
            "! 3.14",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::Not,
                operand_type: "double".to_string()
            }
        );
        test_ok!(unary_not_boolean, "! false", "(!b false)");

        test_ok!(unary_bitwise_not_int, "~ 3", "(~i 3i)");
        test_ko!(
            unary_bitwise_not_double,
            "~ 3.14",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::BitwiseNot,
                operand_type: "double".to_string()
            }
        );
        test_ko!(
            unary_bitwise_not_boolean,
            "~ false",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::BitwiseNot,
                operand_type: "boolean".to_string()
            }
        );

        test_ok!(binary_add_int, "1 + 2", "(+i 1i 2i)");
        test_ok!(binary_add_double, "1.0 + 2.0", "(+d 1d 2d)");
        test_ko!(
            binary_add_int_double,
            "1 + 3.14",
            SemanticAnalysisError::CannotApplyBinaryOperatorToType {
                operator: BinaryOperator::Add,
                left_type: "int".to_string(),
                right_type: "double".to_string(),
            }
        );
        test_ok!(binary_compare, "1 > 2", "(>b 1i 2i)");
    }

    mod blocks {
        use super::*;
        use crate::TypeResolvedBlock;

        macro_rules! test_ok {
            ($name: ident, $source: expr, $expected_typed_ast: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::ParsedAstAllocator::default();
                    let block = parser::parse_as_block(&ast_allocator, $source);

                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_block(block, symbol_table);

                    assert_eq!(
                        TypeResolvedBlock::display(
                            result.expect("should have succeeded semantic analysis")
                        ),
                        $expected_typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::ParsedAstAllocator::default();
                    let block = parser::parse_as_block(&ast_allocator, $source);

                    let analyzer: SemanticAnalyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_block(block, symbol_table);

                    assert_eq!(
                        result
                            .expect_err("should have failed semantic analysis")
                            .to_string(),
                        $expected_error
                    );
                }
            };
        }

        test_ok!(
            return_void,
            r"{
    return;
}",
            r"{ #0
  return;
}
"
        );
        test_ok!(
            return_expr,
            r"{
    return 42;
}",
            r"{ #0
  return 42i;
}
"
        );
        test_ok!(
            single_expression,
            r"{
    1 + 2;
}",
            r"{ #0
  (+i 1i 2i);
}
"
        );
        test_ok!(
            let_single,
            r"{
    let a = 42;
}",
            r"{ #0
  let a: int = 42i;
}
"
        );
        test_ok!(
            let_multiple,
            r"{
    let a = 42, b = true, c = 3.14;
}",
            r"{ #0
  let a: int = 42i, b: boolean = true, c: double = 3.14d;
}
"
        );
        test_ok!(
            let_can_redeclare_symbols,
            r"{
    let a = 42;
    let a = true;
}",
            r"{ #0
  let a: int = 42i;
  let a: boolean = true;
}
"
        );
        test_ok!(
            assignment_valid,
            r"{
    let a = 42;
    a = 43;
}",
            r"{ #0
  let a: int = 42i;
  a = 43i;
}
"
        );
        test_ok!(
            nested_block_basic,
            r"{
  {
    1 + 2;
  }
}",
            r"{ #0
  { #1
    (+i 1i 2i);
  }
}
"
        );
        test_ok!(
            nested_block_can_resolve_variables_declared_in_outer,
            r"{
  let a = 1;
  {
    a = 2;
  }
}",
            r"{ #0
  let a: int = 1i;
  { #1
    a = 2i;
  }
}
"
        );
        test_ok!(
            can_use_declared_variables_in_expressions,
            r"{
  let a = 1;
  a + 1;
}",
            r"{ #0
  let a: int = 1i;
  (+i a 1i);
}
"
        );

        test_ko!(
            assignment_symbol_not_found,
            r"{
    a = 1;
}",
            "symbol not found: \"a\""
        );
        test_ko!(
            assignment_type_mismatch,
            r"{
    let a = 42;
    a = false;
}",
            "invalid assignment to \"a\": symbol has type int, but expression has type boolean"
        );
        test_ko!(
            variables_declared_in_nested_block_cannot_be_accessed_in_outer,
            r"{
  {
    let a = 1;
  }
  a = 2;
}",
            "symbol not found: \"a\""
        );
        test_ko!(
            expression_symbol_not_found,
            r"{
    x;
}",
            "symbol not found: \"x\""
        );
    }

    mod modules {
        use super::*;
        use crate::TypeResolvedModule;

        macro_rules! test_ok {
            ($name: ident, $source: expr, $expected_typed_ast: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::ParsedAstAllocator::default();
                    let module = parser::parse(&ast_allocator, "test", $source);

                    let analyzer = SemanticAnalyzer::default();
                    let result = analyzer.analyze_module(module);

                    assert_eq!(
                        TypeResolvedModule::display(
                            result.expect("should have passed semantic analysis")
                        ),
                        $expected_typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::ParsedAstAllocator::default();
                    let module = parser::parse(&ast_allocator, "test", $source);

                    let analyzer: SemanticAnalyzer = SemanticAnalyzer::default();
                    let result = analyzer.analyze_module(module);

                    assert_eq!(
                        result
                            .expect_err("should have failed semantic analysis")
                            .to_string(),
                        $expected_error
                    );
                }
            };
        }

        #[test]
        fn function_symbol_map_contains_arguments() {
            let ast_allocator = parser::ParsedAstAllocator::default();
            let module = parser::parse(
                &ast_allocator,
                "test",
                "fn inc(x: int) -> int { return 1 + x; }",
            );

            let analyzer: SemanticAnalyzer = SemanticAnalyzer::default();
            let result = analyzer
                .analyze_module(module)
                .expect("should have passed semantic analysis");

            assert_eq!(1, result.functions.len());
            let fun = result.functions[0];
            assert_eq!(1, fun.symbol_table.len());
            let symbol = fun
                .symbol_table
                .lookup_by_name(parser::get_or_create_string("x"))
                .expect("should have found argument x");
            assert_eq!(Type::Int, symbol.symbol_type);
            assert_eq!(
                SymbolKind::Argument {
                    index: ArgumentIndex::from(0)
                },
                symbol.kind
            );
        }

        test_ok!(
            can_use_function_argument_in_expression,
            r"fn inc(x: int) -> int {
  return 1 + x;
}",
            r"module test

fn inc(
  x: int,
) -> int
{ #0
  return (+i 1i x);
}

"
        );
        test_ok!(
            can_assign_to_function_argument,
            r"fn inc(x: int) -> int {
  x = x + 1;
  return x;
}",
            r"module test

fn inc(
  x: int,
) -> int
{ #0
  let x: int = (+i x 1i);
  return x;
}

"
        );

        test_ko!(
            variable_not_found,
            r"fn a() {
    x;
}",
            "symbol not found: \"x\""
        );

        // TODO
        //         test_ko!(
        //             cannot_assign_to_function,
        //             r"fn a() {}
        //
        // fn b() {
        //   a = 1;
        // }",
        //             "symbol not found: \"x\""
        //         );

        // TODO: all return match expected type? here or in separate pass?
    }
}
