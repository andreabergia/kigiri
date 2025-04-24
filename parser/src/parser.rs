// use pest::iterators::Pair;
// use crate::ast::Expression;
// use crate::grammar::Rule;
//
// fn parse_expression(
//     ast: Ast,
//     rule: Pair<'_, Rule>) -> Expression {
//     let pratt = crate::grammar::pratt_parser();
//     pratt
//         .map_primary(|primary| match primary.as_rule() {
//             Rule::number => Expression::LiteralInteger { value: primary.as_str().parse().unwrap() },
//             Rule::identifier => Expression::Identifier(primary.as_str()),
//             Rule::expression => parse_expression(primary),
//             Rule::functionCall => Expression::FunctionCall(parse_function_call(primary)),
//             _ => unreachable!(""),
//         })
//         .map_prefix(|prefix, right| match prefix.as_rule() {
//             Rule::neg => Expression::Negate(Box::new(right)),
//             _ => unreachable!(),
//         })
//         .map_infix(|left, op, right| match op.as_rule() {
//             Rule::add => Expression::Add(Box::new(left), Box::new(right)),
//             Rule::sub => Expression::Sub(Box::new(left), Box::new(right)),
//             Rule::mul => Expression::Mul(Box::new(left), Box::new(right)),
//             Rule::div => Expression::Div(Box::new(left), Box::new(right)),
//             _ => unreachable!(),
//         })
//         .parse(rule.into_inner())
// }
