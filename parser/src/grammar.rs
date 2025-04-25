use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
#[allow(dead_code)]
pub struct Grammar;

#[cfg(test)]
mod tests {
    use super::{Grammar, Rule};
    use pest::Parser;

    fn assert_can_be_parsed_as(input: &str, rule: Rule) {
        let parsed = Grammar::parse(rule, input).unwrap().next().unwrap();
        assert_eq!(input, parsed.as_str());
    }

    fn assert_cannot_be_parsed_as(input: &str, rule: Rule) {
        Grammar::parse(rule, input).expect_err("expected parse to fail");
    }

    #[test]
    fn grammar_can_parse_number() {
        assert_can_be_parsed_as("0", Rule::number);
        assert_can_be_parsed_as("1", Rule::number);
        assert_can_be_parsed_as("123", Rule::number);
        assert_can_be_parsed_as("0x42A", Rule::number);
        assert_can_be_parsed_as("0.123", Rule::number);
        assert_can_be_parsed_as("1.", Rule::number);
        assert_can_be_parsed_as(".1", Rule::number);
        assert_can_be_parsed_as("0.1e+1", Rule::number);
        assert_can_be_parsed_as("1e-0", Rule::number);
        assert_cannot_be_parsed_as(".", Rule::number);
    }

    #[test]
    fn grammar_can_parse_identifier() {
        assert_can_be_parsed_as("x", Rule::identifier);
        assert_can_be_parsed_as("x_32", Rule::identifier);
        assert_can_be_parsed_as("éñò", Rule::identifier);
        assert_cannot_be_parsed_as("1a", Rule::identifier);
    }

    #[test]
    fn grammar_can_parse_function_call() {
        assert_can_be_parsed_as("f()", Rule::functionCall);
        assert_can_be_parsed_as("f(1)", Rule::functionCall);
        assert_can_be_parsed_as("f(a, 3 + b)", Rule::functionCall);
    }

    #[test]
    fn grammar_can_parse_expression() {
        assert_can_be_parsed_as("x", Rule::expression);
        assert_can_be_parsed_as("42", Rule::expression);
        assert_can_be_parsed_as("-3", Rule::expression);
        assert_can_be_parsed_as("f()", Rule::expression);
        assert_can_be_parsed_as("1 + 2", Rule::expression);
        assert_can_be_parsed_as("1 * 2", Rule::expression);
        assert_can_be_parsed_as("1 - 2", Rule::expression);
        assert_can_be_parsed_as("1 / 2", Rule::expression);
        assert_can_be_parsed_as("1 % 2", Rule::expression);
        assert_can_be_parsed_as("1 ** 2", Rule::expression);
        assert_can_be_parsed_as("1 == 2", Rule::expression);
        assert_can_be_parsed_as("1 != 2", Rule::expression);
        assert_can_be_parsed_as("1 < 2", Rule::expression);
        assert_can_be_parsed_as("1 <= 2", Rule::expression);
        assert_can_be_parsed_as("1 > 2", Rule::expression);
        assert_can_be_parsed_as("1 >= 2", Rule::expression);
        assert_can_be_parsed_as("1 && 2", Rule::expression);
        assert_can_be_parsed_as("1 || 2", Rule::expression);
        assert_can_be_parsed_as("1 & 2", Rule::expression);
        assert_can_be_parsed_as("1 | 2", Rule::expression);
        assert_can_be_parsed_as("1 ^ 2", Rule::expression);
        assert_can_be_parsed_as("1 << 2", Rule::expression);
        assert_can_be_parsed_as("1 >> 2", Rule::expression);
        assert_can_be_parsed_as("! 1", Rule::expression);
        assert_can_be_parsed_as("- 1", Rule::expression);
        assert_can_be_parsed_as("~ 1", Rule::expression);
        assert_can_be_parsed_as("-(1 + x) * 4 - f()", Rule::expression);
        assert_can_be_parsed_as("3 * 2 > 2 ^ 5 & ~42 && (1 << x)", Rule::expression);
    }

    #[test]
    fn grammar_can_parse_statement_let() {
        assert_can_be_parsed_as("let x = 1", Rule::letStatement);
        assert_can_be_parsed_as("let y_3π = 1 + x", Rule::letStatement);
    }

    #[test]
    fn grammar_can_parse_statement_assignment() {
        assert_can_be_parsed_as("x = x + 1", Rule::assignmentStatement);
    }

    #[test]
    fn grammar_can_parse_statement_return() {
        assert_can_be_parsed_as("return 42", Rule::returnStatement);
    }

    #[test]
    fn grammar_can_parse_block() {
        assert_can_be_parsed_as("{}", Rule::block);
        assert_can_be_parsed_as("{ x = y; }", Rule::block);
        assert_can_be_parsed_as("{ let x = y; { {} } let z = x; }", Rule::block);
    }

    #[test]
    fn grammar_can_parse_function() {
        assert_can_be_parsed_as("fn main() { let x = y; }", Rule::functionDeclaration);
        assert_can_be_parsed_as("fn f(a) {}", Rule::functionDeclaration);
        assert_can_be_parsed_as("fn f(a, b, c, d, e) {}", Rule::functionDeclaration);
    }

    #[test]
    fn grammar_can_parse_program() {
        assert_can_be_parsed_as("fn main() { }\nfn foo() { let x = 1; }", Rule::program);
    }
}
