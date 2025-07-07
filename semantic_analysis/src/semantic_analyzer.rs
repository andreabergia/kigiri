use crate::phase_top_level_declaration_collector::TopLevelDeclarationCollector;
use crate::phase_type_resolver::TypeResolver;
use crate::{ArgumentIndex, PhaseTypeResolved, SymbolKind, SymbolTable, Type};
use parser::{AstAllocator, BinaryOperator, CompilationPhase, Module, PhaseParsed, UnaryOperator};
use thiserror::Error;

// For the moment I am using _one_ error type for all the passes
// I am unsure if this is better than one error type per pass, but it is
// simpler and I can always split it later.
#[derive(Debug, Error, PartialEq)]
pub enum SemanticAnalysisError {
    #[error("cannot apply operator \"{operator}\" to type {operand_type}")]
    CannotApplyUnaryOperatorToType {
        operator: UnaryOperator,
        operand_type: String,
    },
    #[error("cannot apply operator \"{operator}\" to types {left_type} and {right_type}")]
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
    // TODO: duplicated function name
    #[error("function \"{function_name}\" not found")]
    FunctionNotFound { function_name: String },
}

#[derive(Default)]
pub struct SemanticAnalyzer {
    allocator: AstAllocator,
}

impl SemanticAnalyzer {
    pub fn analyze_module(
        &self,
        module: &Module<PhaseParsed>,
    ) -> Result<&Module<PhaseTypeResolved>, SemanticAnalysisError> {
        // TODO: use the module from phase 1
        TopLevelDeclarationCollector::analyze_module(&self.allocator, module)?;
        TypeResolver::analyze_module(&self.allocator, module)
    }

    pub fn root_symbol_table(&self) -> &SymbolTable {
        SymbolTable::new(&self.allocator, None)
    }
}

#[cfg(test)]
mod tests {
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
            .lookup_by_name(parser::intern_string("x"))
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
        empty,
        r"fn empty() {
  return;
}",
        r"module test

fn empty(
) -> void
{ #0
  return;
}

"
    );
    test_ok!(
        basic_arithmetic_valid,
        r"
fn tests() {
    1;
    1.2;
    true;
    
    -3;
    -3.14;
    !false;
    
    1 + 2;
    3 << 2;
    1.0 * 2.0;
    1 > 2;
    true && false;
}
",
        r"module test

fn tests(
) -> void
{ #0
  1i;
  1.2d;
  true;
  (-i 3i);
  (-d 3.14d);
  (!b false);
  (+i 1i 2i);
  (<<i 3i 2i);
  (*d 1d 2d);
  (>b 1i 2i);
  (&&b true false);
}

"
    );
    test_ok!(
        can_declare_and_use_variables,
        r"fn sum(x: int, y: int, z: int) -> int {
  let sum = x + y;
  sum = sum + z;
  return sum;
}",
        r"module test

fn sum(
  x: int,
  y: int,
  z: int,
) -> int
{ #0
  let sum: int = (+i x y);
  sum = (+i sum z);
  return sum;
}

"
    );
    test_ok!(
        let_multiple_etherogeneous,
        r"fn test() -> boolean {
  let a = 42, b = true, c = 3.14;
  return !b && a > 0 && c < 1.0;
}",
        r"module test

fn test(
) -> boolean
{ #0
  let a: int = 42i, b: boolean = true, c: double = 3.14d;
  return (&&b (&&b (!b b) (>b a 0i)) (<b c 1d));
}

"
    );
    test_ok!(
        can_shadow_variables,
        r"fn test() -> boolean {
  let a = 1;
  let a = true;
  return a;
}",
        r"module test

fn test(
) -> boolean
{ #0
  let a: int = 1i;
  let a: boolean = true;
  return a;
}

"
    );
    test_ok!(
        nested_blocks,
        r"fn test() -> boolean {
  let a = 1;
  {
    return a;
  }
}",
        r"module test

fn test(
) -> boolean
{ #0
  let a: int = 1i;
  { #1
    return a;
  }
}

"
    );

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
    // TODO: function call

    test_ko!(
        invalid_types_neg_boolean,
        "fn test() { - false; }",
        "cannot apply operator \"-\" to type boolean"
    );
    test_ko!(
        invalid_types_not_int,
        "fn test() { ! 1; }",
        "cannot apply operator \"!\" to type int"
    );
    test_ko!(
        invalid_types_not_double,
        "fn test() { ! 3.14; }",
        "cannot apply operator \"!\" to type double"
    );
    test_ko!(
        invalid_types_bitwise_not_double,
        "fn test() { ~ 3.14; }",
        "cannot apply operator \"~\" to type double"
    );
    test_ko!(
        invalid_types_bitwise_not_boolean,
        "fn test() { ~ false; }",
        "cannot apply operator \"~\" to type boolean"
    );
    test_ko!(
        invalid_types_binary_mismatch,
        "fn test() { 1 + 3.14; }",
        "cannot apply operator \"+\" to types int and double"
    );

    test_ko!(
        variable_not_found,
        r"fn a() {
  x;
}",
        "symbol not found: \"x\""
    );
    test_ko!(
        assignment_to_variable_not_found,
        r"fn a() {
  x = 1;
}",
        "symbol not found: \"x\""
    );

    test_ko!(
        assignment_type_mismatch,
        r"fn a() {
  let a = 42;
  a = false;
}",
        "invalid assignment to \"a\": symbol has type int, but expression has type boolean"
    );
    test_ko!(
        variables_declared_in_nested_block_cannot_be_accessed_in_outer,
        r"fn a() {
  { let a = 42; }
  return a;
}",
        "symbol not found: \"a\""
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
