use crate::phase_return_path_analyzer::ReturnPathAnalyzer;
use crate::phase_top_level_declaration_collector::TopLevelDeclarationCollector;
use crate::phase_type_resolver::TypeResolver;
use crate::{PhaseTypeResolved, SymbolTable, Type};
use parser::{AstAllocator, BinaryOperator, Module, PhaseParsed, UnaryOperator};
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
    #[error("\"{name}\" is not a function")]
    NotAFunction { name: String },
    #[error(
        "not enough arguments in call to \"{function_name}\": expected {expected}, found {found}"
    )]
    ArgumentCountMismatchTooFew {
        function_name: String,
        expected: usize,
        found: usize,
    },
    #[error(
        "too many arguments in call to \"{function_name}\": expected {expected}, found {found}"
    )]
    ArgumentCountMismatchTooMany {
        function_name: String,
        expected: usize,
        found: usize,
    },
    #[error(
        "argument type mismatch in call to \"{function_name}\": argument {argument_index} ({parameter_name}) expected {expected_type}, found {actual_type}"
    )]
    ArgumentTypeMismatch {
        function_name: String,
        argument_index: usize,
        parameter_name: String,
        expected_type: Type,
        actual_type: String,
    },
    #[error("if condition must be of type bool, found {actual_type}")]
    IfConditionMustBeBool { actual_type: String },
    #[error("while condition must be of type bool, found {actual_type}")]
    WhileConditionMustBeBool { actual_type: String },
    #[error("break statement outside of loop")]
    BreakOutsideLoop,
    #[error("continue statement outside of loop")]
    ContinueOutsideLoop,
    #[error("internal error: {message}")]
    InternalError { message: String },
    #[error("function \"{function_name}\" does not return a value on all paths")]
    NotAllPathsReturnAValue { function_name: String },
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
        let module = TopLevelDeclarationCollector::analyze_module(&self.allocator, module)?;
        let module = TypeResolver::analyze_module(&self.allocator, module)?;
        ReturnPathAnalyzer::analyze_module(module)?;
        Ok(module)
    }

    pub fn root_symbol_table(&self) -> &SymbolTable {
        SymbolTable::new(&self.allocator, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArgumentIndex, SymbolKind, TypeResolvedModule};
    use kigiri_memory::intern_string;

    macro_rules! test_ok {
        ($name: ident, $source: expr, $expected_typed_ast: expr) => {
            #[test]
            fn $name() {
                let ast_allocator = parser::ParsedAstAllocator::default();
                let module =
                    parser::parse(&ast_allocator, "test", $source).expect("parse should succeed");

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
        ($name: ident, $source: expr) => {
            #[test]
            fn $name() {
                let ast_allocator = parser::ParsedAstAllocator::default();
                let module =
                    parser::parse(&ast_allocator, "test", $source).expect("parse should succeed");

                let analyzer = SemanticAnalyzer::default();
                analyzer
                    .analyze_module(module)
                    .expect("should have passed semantic analysis");
            }
        };
    }

    macro_rules! test_ko {
        ($name: ident, $source: expr, $expected_error: expr) => {
            #[test]
            fn $name() {
                let ast_allocator = parser::ParsedAstAllocator::default();
                let module =
                    parser::parse(&ast_allocator, "test", $source).expect("parse should succeed");

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
            "fn inc(x: i32) -> i32 { return 1i32 + x; }",
        )
        .expect("parse should succeed");

        let analyzer: SemanticAnalyzer = SemanticAnalyzer::default();
        let result = analyzer
            .analyze_module(module)
            .expect("should have passed semantic analysis");

        assert_eq!(1, result.functions.len());
        let fun = result.functions[0];
        assert_eq!(1, fun.symbol_table.len());
        let symbol = fun
            .symbol_table
            .lookup_by_name(intern_string("x"))
            .expect("should have found argument x");
        assert_eq!(
            SymbolKind::Argument {
                argument_type: Type::I32,
                index: ArgumentIndex::from(0)
            },
            symbol.kind
        );
        assert_eq!(Some(Type::I32), symbol.symbol_type());
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
  1i32;
  1.2f64;
  true;
  (-i32 3i32);
  (-f64 3.14f64);
  (!b false);
  (+i32 1i32 2i32);
  (<<i32 3i32 2i32);
  (*f64 1f64 2f64);
  (>b 1i32 2i32);
  (&&b true false);
}

"
    );
    test_ok!(
        can_declare_and_use_variables,
        r"fn sum(x: i32, y: i32, z: i32) -> i32 {
  let sum = x + y;
  sum = sum + z;
  return sum;
}",
        r"module test

fn sum(
  x: i32,
  y: i32,
  z: i32,
) -> i32
{ #0
  let sum: i32 = (+i32 x y);
  sum = (+i32 sum z);
  return sum;
}

"
    );
    test_ok!(
        let_multiple_etherogeneous,
        r"fn test() -> bool {
  let a = 42i64, b = true, c = 3.14;
  return !b && a > 0i64 && c < 1.0;
}",
        r"module test

fn test(
) -> bool
{ #0
  let a: i64 = 42i64, b: bool = true, c: f64 = 3.14f64;
  return (&&b (&&b (!b b) (>b a 0i64)) (<b c 1f64));
}

"
    );
    test_ok!(
        can_shadow_variables,
        r"fn test() -> bool {
  let a = 1i16;
  let a = true;
  return a;
}",
        r"module test

fn test(
) -> bool
{ #0
  let a: i16 = 1i16;
  let a: bool = true;
  return a;
}

"
    );
    test_ok!(
        nested_blocks,
        r"fn test() -> bool {
  let a = 1i8;
  {
    return a;
  }
}",
        r"module test

fn test(
) -> bool
{ #0
  let a: i8 = 1i8;
  { #1
    return a;
  }
}

"
    );

    test_ok!(
        can_use_function_argument_in_expression,
        r"fn inc(x: i32) -> i32 {
  return 1 + x;
}",
        r"module test

fn inc(
  x: i32,
) -> i32
{ #0
  return (+i32 1i32 x);
}

"
    );
    test_ok!(
        can_assign_to_function_argument,
        r"fn inc(x: i32) -> i32 {
  x = x + 1;
  return x;
}",
        r"module test

fn inc(
  x: i32,
) -> i32
{ #0
  let x: i32 = (+i32 x 1i32);
  return x;
}

"
    );
    test_ok!(
        function_call_no_args,
        r#"
fn f() -> i8 { return 42i8; }
fn main() -> i8 { return f(); }"#,
        r#"module test

fn f(
) -> i8
{ #0
  return 42i8;
}

fn main(
) -> i8
{ #0
  return f();
}

"#
    );
    test_ok!(
        function_call_with_args,
        r#"
fn inc(x: i16) -> i16 { return x + 1i16; }
fn main() -> i16 { return inc(41i16); }"#,
        r#"module test

fn inc(
  x: i16,
) -> i16
{ #0
  return (+i16 x 1i16);
}

fn main(
) -> i16
{ #0
  return inc(41i16);
}

"#
    );
    test_ok!(
        function_call_void,
        r#"
fn empty() { }
fn main() { empty(); }"#,
        r#"module test

fn empty(
) -> void
{ #0
}

fn main(
) -> void
{ #0
  empty();
}

"#
    );

    test_ko!(
        invalid_types_neg_bool,
        "fn test() { - false; }",
        "cannot apply operator \"-\" to type bool"
    );
    test_ko!(
        invalid_types_not_int,
        "fn test() { ! 1; }",
        "cannot apply operator \"!\" to type i32"
    );
    test_ko!(
        invalid_types_not_double,
        "fn test() { ! 3.14; }",
        "cannot apply operator \"!\" to type f64"
    );
    test_ko!(
        invalid_types_bitwise_not_double,
        "fn test() { ~ 3.14; }",
        "cannot apply operator \"~\" to type f64"
    );
    test_ko!(
        invalid_types_bitwise_not_bool,
        "fn test() { ~ false; }",
        "cannot apply operator \"~\" to type bool"
    );
    test_ko!(
        invalid_types_binary_mismatch,
        "fn test() { 1 + 3.14; }",
        "cannot apply operator \"+\" to types i32 and f64"
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
        "invalid assignment to \"a\": symbol has type i32, but expression has type bool"
    );
    test_ko!(
        variables_declared_in_nested_block_cannot_be_accessed_in_outer,
        r"fn a() {
  { let a = 42; }
  return a;
}",
        "symbol not found: \"a\""
    );
    test_ko!(
        cannot_use_variable_just_declared_in_rhs,
        r"fn test() {
  let x = x + 1;
}",
        "symbol not found: \"x\""
    );
    test_ko!(
        function_not_found,
        r#"fn main() -> i32 {
  return f();
}"#,
        r#"function "f" not found"#
    );
    test_ko!(
        calling_a_non_function_symbol,
        r#"fn main() -> i32 {
  let f = 42;
  return f();
}"#,
        r#""f" is not a function"#
    );
    test_ko!(
        calling_a_shadowed_function,
        r#"
fn f() -> i32 { return 42; }
fn main() -> i32 {
  let f = 42;
  return f();
}"#,
        r#""f" is not a function"#
    );
    test_ko!(
        assigning_a_void_function_call,
        r#"
fn empty() { }
fn main() {
  let x = empty();
}"#,
        r#"cannot assign void value to variable "x""#
    );
    test_ko!(
        cannot_assign_to_function,
        r"fn a() {}

    fn b() {
      a = 1;
    }",
        "cannot assign value to function \"a\""
    );
    test_ko!(
        argument_to_function_call_number_mismatch_too_few,
        r"
fn f(x: i32) {}
fn main() { f(); }",
        "not enough arguments in call to \"f\": expected 1, found 0"
    );
    test_ko!(
        argument_to_function_call_number_mismatch_too_many,
        r"
fn f() {}
fn main() { f(1); }",
        "too many arguments in call to \"f\": expected 0, found 1"
    );
    test_ko!(
        argument_type_mismatch_int_to_bool,
        r"
fn f(x: bool) {}
fn main() { f(42); }",
        "argument type mismatch in call to \"f\": argument 0 (x) expected bool, found i32"
    );
    test_ko!(
        argument_type_mismatch_void_to_int,
        r"
fn empty() {}
fn f(x: i32) {}
fn main() { f(empty()); }",
        "argument type mismatch in call to \"f\": argument 0 (x) expected i32, found void"
    );

    // If statement tests
    test_ok!(
        if_statement_simple,
        r"fn test() {
  if true {
    return;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  if true { #1
    return;
  }
}

"
    );

    test_ok!(
        if_statement_with_else,
        r"fn test() {
  if false {
    let x = 1;
  } else {
    let y = 2;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  if false { #1
    let x: i32 = 1i32;
  }
  else { #2
    let y: i32 = 2i32;
  }
}

"
    );

    test_ok!(
        if_statement_with_else_if,
        r"fn test() {
  if false {
    let x = 1;
  } else if true {
    let y = 2;
  } else {
    let z = 3;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  if false { #1
    let x: i32 = 1i32;
  }
  else   if true { #2
    let y: i32 = 2i32;
  }
  else { #3
    let z: i32 = 3i32;
  }
}

"
    );

    test_ok!(
        if_statement_with_expression_condition,
        r"fn test(x: i16) {
  if x > 0i16 {
    return;
  }
}",
        r"module test

fn test(
  x: i16,
) -> void
{ #0
  if (>b x 0i16) { #1
    return;
  }
}

"
    );

    test_ok!(
        if_statement_variable_scoping,
        r"fn test() {
  let x = 1;
  if true {
    let x = 2; 
    x;
  }
  x;
}",
        r"module test

fn test(
) -> void
{ #0
  let x: i32 = 1i32;
  if true { #1
    let x: i32 = 2i32;
    x;
  }
  x;
}

"
    );

    test_ok!(
        nested_if_statements,
        r"fn test() {
  if true {
    if false {
      let x = 1i16;
    }
  }
}",
        r"module test

fn test(
) -> void
{ #0
  if true { #1
    if false { #2
      let x: i16 = 1i16;
    }
  }
}

"
    );

    test_ko!(
        if_condition_must_be_bool_int,
        r"fn test() {
  if 42 {
    return;
  }
}",
        "if condition must be of type bool, found i32"
    );

    test_ko!(
        if_condition_must_be_bool_double,
        r"fn test() {
  if 3.14 {
    return;
  }
}",
        "if condition must be of type bool, found f64"
    );

    test_ko!(
        if_condition_must_be_bool_void,
        r"fn empty() {}
fn test() {
  if empty() {
    return;
  }
}",
        "if condition must be of type bool, found void"
    );

    test_ko!(
        if_condition_must_be_bool_else_if,
        r"fn test() {
  if true {
    return;
  } else if 1 {
    return;
  }
}",
        "if condition must be of type bool, found i32"
    );

    test_ok!(
        variable_can_be_declared_in_ifs,
        r"
fn test(condition: bool) -> i32 {
    let r = 1;
    if condition {
        let x = 2;
        return x + r;
    }
    return r;
}",
        r"module test

fn test(
  condition: bool,
) -> i32
{ #0
  let r: i32 = 1i32;
  if condition { #1
    let x: i32 = 2i32;
    return (+i32 x r);
  }
  return r;
}

"
    );

    // While statement tests
    test_ok!(
        while_statement_simple,
        r"fn test() {
  while true {
    return;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  while true { #1
    return;
  }
}

"
    );

    test_ko!(
        while_condition_must_be_bool,
        r"fn test() {
  while 42 {
    return;
  }
}",
        "while condition must be of type bool, found i32"
    );

    // Break and continue statement tests
    test_ok!(
        break_in_while_loop,
        r"fn test() {
  while true {
    break;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  while true { #1
    break;
  }
}

"
    );

    test_ok!(
        continue_in_while_loop,
        r"fn test() {
  while true {
    continue;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  while true { #1
    continue;
  }
}

"
    );

    test_ok!(
        break_and_continue_in_nested_blocks,
        r"fn test() {
  while true {
    if true {
      break;
    } else {
      continue;
    }
  }
}",
        r"module test

fn test(
) -> void
{ #0
  while true { #1
    if true { #2
      break;
    }
    else { #3
      continue;
    }
  }
}

"
    );

    test_ko!(
        break_outside_loop,
        r"fn test() {
  break;
}",
        "break statement outside of loop"
    );

    test_ko!(
        continue_outside_loop,
        r"fn test() {
  continue;
}",
        "continue statement outside of loop"
    );

    test_ko!(
        break_in_if_outside_loop,
        r"fn test() {
  if true {
    break;
  }
}",
        "break statement outside of loop"
    );

    test_ko!(
        continue_in_if_outside_loop,
        r"fn test() {
  if true {
    continue;
  }
}",
        "continue statement outside of loop"
    );

    // Loop statement tests
    test_ok!(
        loop_statement_simple,
        r"fn test() {
  loop {
    return;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  loop { #1
    return;
  }
}

"
    );

    test_ok!(
        break_in_loop_statement,
        r"fn test() {
  loop {
    break;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  loop { #1
    break;
  }
}

"
    );

    test_ok!(
        continue_in_loop_statement,
        r"fn test() {
  loop {
    continue;
  }
}",
        r"module test

fn test(
) -> void
{ #0
  loop { #1
    continue;
  }
}

"
    );

    test_ok!(
        break_and_continue_in_loop_with_condition,
        r"fn test() {
  loop {
    if true {
      break;
    } else {
      continue;
    }
  }
}",
        r"module test

fn test(
) -> void
{ #0
  loop { #1
    if true { #2
      break;
    }
    else { #3
      continue;
    }
  }
}

"
    );

    test_ok!(
        nested_loop_statements,
        r"fn test() {
  loop {
    loop {
      break;
    }
  }
}",
        r"module test

fn test(
) -> void
{ #0
  loop { #1
    loop { #2
      break;
    }
  }
}

"
    );

    test_ko!(
        not_all_paths_return_expr,
        r#"
fn f(x: i32) -> i32 {
    f(x - 1);
}"#,
        r#"function "f" does not return a value on all paths"#
    );

    test_ko!(
        not_all_paths_return_if,
        r#"
fn f(x: i32) -> i32 {
    if x > 0 {
        return 1;
    }
}"#,
        r#"function "f" does not return a value on all paths"#
    );

    test_ok!(
        all_paths_return_if_else,
        r#"
fn f(x: i32) -> i32 {
    if x > 0 {
        return 1;
    } else {
        return -1;
    }
}"#
    );

    test_ok!(
        all_paths_return_if_else_if,
        r#"
fn f(x: i32) -> i32 {
    if x > 0 {
        return 1;
    } else if x < 0 {
        return -1;
    } else {
        return 0;
    }
}"#
    );

    test_ok!(
        infinite_loop_is_ok,
        r#"
fn f() -> i32 {
    loop {}
}"#
    );

    test_ko!(
        while_is_not_ok,
        r#"
fn f(x: i32) -> i32 {
    while x > 0 {
        x = x - 1;
    }
}"#,
        r#"function "f" does not return a value on all paths"#
    );

    test_ko!(
        infinite_loop_with_break_is_not_ok,
        r#"
fn f(x: i32) -> i32 {
    loop {
        break;
    }
    loop {
        if x > 0 {
            continue;
        } else if x < 0 {
            f(x + 1);
        } else {
            continue;
        }
        while true { }
        loop { }
        f(x - 1);
        {
            break;
        }
    }
}"#,
        r#"function "f" does not return a value on all paths"#
    );
}
