use crate::ast::{Ast, Expression};
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
        // .map_prefix(|prefix, right| match prefix.as_rule() {
        //     Rule::neg => Expression::Negate(Box::new(right)),
        //     _ => unreachable!(),
        // })
        .map_infix(|left, op, right| match op.as_rule() {
            Rule::add => ast.add(left, right),
            // Rule::sub => Expression::Sub(Box::new(left), Box::new(right)),
            // Rule::mul => Expression::Mul(Box::new(left), Box::new(right)),
            // Rule::div => Expression::Div(Box::new(left), Box::new(right)),
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

        let pair = Grammar::parse(Rule::expression, "3 + x")
            .unwrap()
            .next()
            .unwrap();
        let expression = parse_expression(&ast, pair);

        assert_eq!(expression.to_string(), "(+ 3i x)");
    }
}
