use crate::ast::{Ast, BinaryOperator, Expression, UnaryOperator};
use crate::grammar::Rule;
use pest::iterators::Pair;

fn parse_expression<'ast>(ast: &'ast Ast, rule: Pair<'_, Rule>) -> &'ast Expression<'ast> {
    let pratt = crate::grammar::pratt_parser();
    pratt
        .map_primary(|primary| match primary.as_rule() {
            Rule::number => ast.literal_integer(primary.as_str().parse().unwrap()),
            Rule::identifier => ast.identifier(primary.as_str()),
            Rule::expression => parse_expression(ast, primary),
            // Rule::functionCall => Expression::FunctionCall(parse_function_call(primary)),
            _ => unreachable!(""),
        })
        .map_prefix(|prefix, operand| match prefix.as_rule() {
            Rule::neg => ast.unary(UnaryOperator::Neg, operand),
            _ => unreachable!(),
        })
        .map_infix(|left, op, right| match op.as_rule() {
            Rule::add => ast.binary(BinaryOperator::Add, left, right),
            Rule::mul => ast.binary(BinaryOperator::Mul, left, right),
            Rule::sub => ast.binary(BinaryOperator::Sub, left, right),
            Rule::div => ast.binary(BinaryOperator::Div, left, right),
            _ => unreachable!(),
        })
        .parse(rule.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::Grammar;
    use pest::Parser;

    #[test]
    fn test_parse_sum_expression() {
        let ast = Ast::for_tests();

        let pair = Grammar::parse(Rule::expression, "3 + x * true + -2")
            .unwrap()
            .next()
            .unwrap();
        let expression = parse_expression(&ast, pair);

        assert_eq!(expression.to_string(), "(+ (+ 3i (* x true)) (- 2i))");
    }
}
