use crate::ast::{
    Ast, BinaryOperator, Block, Expression, FunctionArgument, FunctionDeclaration,
    FunctionSignaturesByName, LetInitializer, Module, Statement, UnaryOperator,
};
use crate::grammar::{Grammar, Rule};
use crate::symbols::get_or_create_string;
use bumpalo::collections::Vec as BumpVec;
use pest::iterators::Pair;
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest::Parser;
use std::str::FromStr;
use std::sync::LazyLock;

static PRATT_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
    PrattParser::new()
        .op(Op::infix(Rule::or, Assoc::Left))
        .op(Op::infix(Rule::and, Assoc::Left))
        .op(Op::infix(Rule::bitwise_and, Assoc::Left)
            | Op::infix(Rule::bitwise_or, Assoc::Left)
            | Op::infix(Rule::bitwise_xor, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left) | Op::infix(Rule::neq, Assoc::Left))
        .op(Op::infix(Rule::lt, Assoc::Left)
            | Op::infix(Rule::lte, Assoc::Left)
            | Op::infix(Rule::gt, Assoc::Left)
            | Op::infix(Rule::gte, Assoc::Left))
        .op(Op::infix(Rule::bitwise_shl, Assoc::Left) | Op::infix(Rule::bitwise_shr, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left)
            | Op::infix(Rule::div, Assoc::Left)
            | Op::infix(Rule::rem, Assoc::Left))
        .op(Op::infix(Rule::exp, Assoc::Right))
        .op(Op::prefix(Rule::neg) | Op::prefix(Rule::not) | Op::prefix(Rule::bitwise_not))
});

fn parse_expression<'ast>(ast: &'ast Ast, rule: Pair<'_, Rule>) -> &'ast Expression<'ast> {
    PRATT_PARSER
        .map_primary(|primary| {
            match primary.as_rule() {
                Rule::number => {
                    let pair = primary.into_inner().next().unwrap();
                    let text = pair.as_str();
                    match pair.as_rule() {
                        Rule::integerNumber => ast.literal_integer(i64::from_str(text).unwrap()),
                        Rule::hexNumber => ast.literal_integer(
                            i64::from_str_radix(
                                text.to_ascii_lowercase().trim_start_matches("0x"),
                                16,
                            )
                            .unwrap(),
                        ),
                        Rule::doubleNumber => ast.literal_double(f64::from_str(text).unwrap()),
                        _ => unreachable!(""),
                    }
                }
                Rule::identifier => ast.identifier(primary.as_str()),
                Rule::expression => parse_expression(ast, primary),
                Rule::boolean => ast.literal_boolean(primary.as_str().parse().unwrap()),
                // Rule::functionCall => Expression::FunctionCall(parse_function_call(primary)),
                _ => unreachable!(""),
            }
        })
        .map_prefix(|prefix, operand| match prefix.as_rule() {
            Rule::neg => ast.unary(UnaryOperator::Neg, operand),
            Rule::not => ast.unary(UnaryOperator::Not, operand),
            Rule::bitwise_not => ast.unary(UnaryOperator::BitwiseNot, operand),
            _ => unreachable!(),
        })
        .map_infix(|left, op, right| match op.as_rule() {
            Rule::add => ast.binary(BinaryOperator::Add, left, right),
            Rule::mul => ast.binary(BinaryOperator::Mul, left, right),
            Rule::sub => ast.binary(BinaryOperator::Sub, left, right),
            Rule::div => ast.binary(BinaryOperator::Div, left, right),
            Rule::rem => ast.binary(BinaryOperator::Rem, left, right),
            Rule::exp => ast.binary(BinaryOperator::Exp, left, right),
            Rule::eq => ast.binary(BinaryOperator::Eq, left, right),
            Rule::neq => ast.binary(BinaryOperator::Neq, left, right),
            Rule::lt => ast.binary(BinaryOperator::Lt, left, right),
            Rule::lte => ast.binary(BinaryOperator::Lte, left, right),
            Rule::gt => ast.binary(BinaryOperator::Gt, left, right),
            Rule::gte => ast.binary(BinaryOperator::Gte, left, right),
            Rule::and => ast.binary(BinaryOperator::And, left, right),
            Rule::or => ast.binary(BinaryOperator::Or, left, right),
            Rule::bitwise_and => ast.binary(BinaryOperator::BitwiseAnd, left, right),
            Rule::bitwise_or => ast.binary(BinaryOperator::BitwiseOr, left, right),
            Rule::bitwise_xor => ast.binary(BinaryOperator::BitwiseXor, left, right),
            Rule::bitwise_shl => ast.binary(BinaryOperator::BitwiseShl, left, right),
            Rule::bitwise_shr => ast.binary(BinaryOperator::BitwiseShr, left, right),
            _ => unreachable!(),
        })
        .parse(rule.into_inner())
}

fn parse_let_statement<'ast>(ast: &'ast Ast, rule: Pair<'_, Rule>) -> &'ast Statement<'ast> {
    let mut iter = rule.into_inner();
    let mut initializers = ast.statement_let_initializers();
    loop {
        let Some(initializer_rule) = iter.next() else {
            break;
        };
        let mut initializer_rule = initializer_rule.into_inner();

        let id = initializer_rule.next().unwrap();
        let id = get_or_create_string(id.as_str());

        let value = initializer_rule.next().map(|e| parse_expression(ast, e));

        initializers.push(LetInitializer { name: id, value })
    }
    ast.statement_let(initializers)
}

fn parse_statement<'ast>(ast: &'ast Ast, rule: Pair<'_, Rule>) -> &'ast Statement<'ast> {
    let pair = rule.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::letStatement => parse_let_statement(ast, pair),
        Rule::assignmentStatement => {
            let mut inner = pair.into_inner();
            let identifier = inner
                .next()
                .expect("identifier on lhs of assignment")
                .as_str();
            let expression =
                parse_expression(ast, inner.next().expect("expression on rhs of assignment"));
            ast.statement_assignment(identifier, expression)
        }
        Rule::returnStatement => {
            let expression = pair.into_inner().next().map(|p| parse_expression(ast, p));
            ast.statement_return(expression)
        }
        Rule::expression => {
            let expression = parse_expression(ast, pair);
            ast.statement_expression(expression)
        }
        _ => unreachable!(),
    }
}

fn parse_block<'ast>(ast: &'ast Ast, rule: Pair<'_, Rule>) -> &'ast Block<'ast> {
    // We want a parent block to have a smaller id than any nested block,
    // so we generate the block_id first and then recurse.
    let block_id = ast.next_block_id();

    let mut statements = ast.statements();
    for pair in rule.into_inner() {
        match pair.as_rule() {
            Rule::statement => statements.push(parse_statement(ast, pair)),
            Rule::block => statements.push(ast.nested_block(parse_block(ast, pair))),
            _ => unreachable!(),
        }
    }
    ast.block_from_statements(block_id, statements)
}

fn parse_function_declaration_arguments<'ast>(
    ast: &'ast Ast,
    rule: Pair<'_, Rule>,
) -> BumpVec<'ast, FunctionArgument> {
    let mut arguments = ast.function_arguments();

    for arg in rule.into_inner() {
        let mut arg = arg.into_inner();
        let name = arg.next().expect("argument name").as_str();
        let arg_type = arg.next().expect("argument type").as_str();
        arguments.push(FunctionArgument {
            name: get_or_create_string(name),
            arg_type: get_or_create_string(arg_type),
        })
    }

    arguments
}

fn parse_function_declaration<'ast>(
    ast: &'ast Ast,
    rule: Pair<'_, Rule>,
) -> &'ast FunctionDeclaration<'ast> {
    let mut rule_iter = rule.into_inner();
    let name = rule_iter.next().expect("function name").as_str();

    let arguments_rule = rule_iter.next().expect("function arguments");
    let arguments = parse_function_declaration_arguments(ast, arguments_rule);

    let next = rule_iter.next().expect("function return type or body");
    let (return_type, body_rule) = if let Rule::functionReturnType = next.as_rule() {
        let return_type = next.into_inner().next().expect("return type").as_str();
        (
            Some(get_or_create_string(return_type)),
            rule_iter.next().expect("function body"),
        )
    } else {
        (None, next)
    };

    let body = parse_block(ast, body_rule);

    assert!(rule_iter.next().is_none());

    ast.function_declaration(name, return_type, arguments, body)
}

fn parse_module<'ast>(
    ast: &'ast Ast,
    module_name: &str,
    rule: Pair<'_, Rule>,
) -> &'ast Module<'ast> {
    let mut functions = ast.functions();
    let mut function_signatures = FunctionSignaturesByName::default();

    let rule_inner = rule.into_inner();
    for inner in rule_inner.into_iter() {
        match inner.as_rule() {
            Rule::EOI => continue,
            Rule::functionDeclaration => {
                let fun = parse_function_declaration(ast, inner);
                function_signatures.insert(fun.signature.name, fun.signature);
                functions.push(fun);
            }
            _ => unreachable!(),
        }
    }

    ast.module(module_name, functions, function_signatures)
}

pub fn parse_as_expression<'ast>(ast: &'ast Ast, text: &str) -> &'ast Expression<'ast> {
    let pair = Grammar::parse(Rule::expression, text)
        .unwrap()
        .next()
        .unwrap();
    parse_expression(ast, pair)
}

pub fn parse_as_block<'ast>(ast: &'ast Ast, text: &str) -> &'ast Block<'ast> {
    let pair = Grammar::parse(Rule::block, text).unwrap().next().unwrap();
    parse_block(ast, pair)
}

pub fn parse<'ast>(ast: &'ast Ast, module_name: &str, text: &str) -> &'ast Module<'ast> {
    let pair = Grammar::parse(Rule::module, text).unwrap().next().unwrap();
    parse_module(ast, module_name, pair)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Generates a test case to verify the AST produced by a given source expression.
    /// The AST is passed as its string representation.
    /// The macro allows us to one-line a test case, reducing noise such as the
    /// `#[test]` annotation and the various newline required by a function.
    macro_rules! test_expression {
        ($name: ident, $source: expr, $ast: expr) => {
            #[test]
            fn $name() {
                let ast = Ast::default();
                let expression = parse_as_expression(&ast, $source);
                assert_eq!(expression.to_string(), $ast);
            }
        };
    }

    macro_rules! test_block {
        ($name: ident, $source: expr, $ast: expr) => {
            #[test]
            fn $name() {
                let ast = Ast::default();
                let block = parse_as_block(&ast, $source);
                assert_eq!(block.to_string(), $ast);
            }
        };
    }

    test_expression!(literal_int_1, "1", "1i");
    test_expression!(literal_int_2, "3217832", "3217832i");
    test_expression!(literal_int_3, "0xA1", "161i");

    test_expression!(literal_float_1, "0.", "0d");
    test_expression!(literal_float_2, "3.14", "3.14d");
    test_expression!(literal_float_3, "1.1e+2", "110d");
    test_expression!(literal_float_4, "10e-1", "1d");
    test_expression!(literal_float_5, ".1e1", "1d");
    test_expression!(literal_float_6, "1e4", "10000d");

    test_expression!(identifier_1, "i", "i");
    test_expression!(identifier_2, "a_b", "a_b");
    test_expression!(identifier_3, "éñò", "éñò");
    test_expression!(identifier_4, "_a", "_a");
    test_expression!(identifier_5, "_", "_");

    test_expression!(boolean_1, "true", "true");
    test_expression!(boolean_2, "false", "false");

    test_expression!(precedence_01, "1 + 2 * 3", "(+ 1i (* 2i 3i))");
    test_expression!(precedence_02, "1 - 2 / 3", "(- 1i (/ 2i 3i))");
    test_expression!(precedence_03, "1 + 2 % 3", "(+ 1i (% 2i 3i))");
    test_expression!(precedence_04, "1 * 2 ** 3", "(* 1i (** 2i 3i))");
    test_expression!(precedence_05, "1 == 2 + 3", "(== 1i (+ 2i 3i))");
    test_expression!(precedence_06, "1 != 2 + 3", "(!= 1i (+ 2i 3i))");
    test_expression!(precedence_07, "1 < 2 + 3", "(< 1i (+ 2i 3i))");
    test_expression!(precedence_08, "1 <= 2 + 3", "(<= 1i (+ 2i 3i))");
    test_expression!(precedence_09, "1 > 2 + 3", "(> 1i (+ 2i 3i))");
    test_expression!(precedence_10, "1 >= 2 + 3", "(>= 1i (+ 2i 3i))");
    test_expression!(precedence_11, "1 && 2 == 3", "(&& 1i (== 2i 3i))");
    test_expression!(precedence_12, "1 || 2 && 3", "(|| 1i (&& 2i 3i))");
    test_expression!(precedence_13, "1 & 2 + 3", "(& 1i (+ 2i 3i))");
    test_expression!(precedence_14, "1 + 2 | 3", "(| (+ 1i 2i) 3i)");
    test_expression!(precedence_15, "1 ^ 2 == 3", "(^ 1i (== 2i 3i))");
    test_expression!(precedence_16, "1 | 2 && 3", "(&& (| 1i 2i) 3i)");
    test_expression!(precedence_17, "1 + 2 << 3", "(<< (+ 1i 2i) 3i)");
    test_expression!(precedence_18, "1 == 2 >> 3", "(== 1i (>> 2i 3i))");
    test_expression!(precedence_19, "1 == 2 > 3", "(== 1i (> 2i 3i))");
    test_expression!(precedence_20, "1 != 2 <= 3", "(!= 1i (<= 2i 3i))");
    test_expression!(precedence_21, "1 + - 2", "(+ 1i (- 2i))");
    test_expression!(precedence_22, "1 + ~ 2", "(+ 1i (~ 2i))");
    test_expression!(precedence_23, "1 && ! 2", "(&& 1i (! 2i))");

    test_expression!(parenthesis, "(1 + 2) * 3", "(* (+ 1i 2i) 3i)");

    test_block!(
        statement_expression,
        r"{
   1;
}",
        r"{ #0
1i;
}"
    );
    test_block!(
        statement_return_with_value,
        r"{
   return 1;
}",
        r"{ #0
return 1i;
}"
    );
    test_block!(
        statement_return_empty,
        r"{
   return;
}",
        r"{ #0
return;
}"
    );
    test_block!(
        statement_let_initializer,
        r"{
   let a = 1;
}",
        r"{ #0
let a = 1i;
}"
    );
    test_block!(
        statement_let_no_initializer,
        r"{
   let a;
}",
        r"{ #0
let a;
}"
    );
    test_block!(
        statement_let_multiple_initializers,
        r"{
   let a = 1, b;
}",
        r"{ #0
let a = 1i, b;
}"
    );
    test_block!(
        statement_assignment,
        r"{
   a = 1;
}",
        r"{ #0
a = 1i;
}"
    );
    test_block!(
        statement_nested_block,
        r"{
       {
          a = 1;
       }
    }",
        r"{ #0
{ #1
a = 1i;
}
}"
    );

    #[test]
    fn module_fn_with_return_type() {
        let ast = Ast::default();
        let module = parse(
            &ast,
            "test",
            r"
fn add(x: int, y: int) -> int {
    return x + y;
}
",
        );
        assert_eq!(
            module.to_string(),
            r"module test

fn add(
    x: int,
    y: int,
) -> int
{ #0
return (+ x y);
}
"
        );
    }

    #[test]
    fn module_fn_no_return_type() {
        let ast = Ast::default();
        let module = parse(
            &ast,
            "test",
            r"
fn foo() {}
",
        );
        assert_eq!(
            module.to_string(),
            r"module test

fn foo(
) -> void
{ #0
}
"
        );
    }
}
