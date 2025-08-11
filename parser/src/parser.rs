use crate::ast::{
    BinaryOperator, Block, Expression, FunctionArgument, FunctionDeclaration, IfElseBlock,
    LetInitializer, Module, Statement, UnaryOperator,
};
use crate::error::{ParseError, ParseResult};
use crate::grammar::{Grammar, Rule};
use crate::parsed_ast::{FunctionSignaturesByName, ParsedAstAllocator, PhaseParsed};
use kigiri_memory::{BumpVec, intern_string};
use pest::Parser;
use pest::iterators::Pair;
use pest::pratt_parser::{Assoc, Op, PrattParser};
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

fn parse_expression<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Expression<'a, PhaseParsed<'a>>> {
    PRATT_PARSER
        .map_primary(|primary| -> ParseResult<_> {
            match primary.as_rule() {
                Rule::number => {
                    let pair =
                        primary
                            .into_inner()
                            .next()
                            .ok_or_else(|| ParseError::InternalError {
                                message: "expected a number literal".to_owned(),
                            })?;
                    let text = pair.as_str();
                    match pair.as_rule() {
                        Rule::intNumber => {
                            let value = i64::from_str(text).map_err(|source| {
                                ParseError::IntegerParseError {
                                    text: text.to_owned(),
                                    source,
                                }
                            })?;
                            Ok(ast_allocator.literal_int(value))
                        }
                        Rule::hexNumber => {
                            let lowercase_text = text.to_ascii_lowercase();
                            let hex_text = lowercase_text.trim_start_matches("0x");
                            let value = i64::from_str_radix(hex_text, 16).map_err(|source| {
                                ParseError::IntegerParseError {
                                    text: text.to_owned(),
                                    source,
                                }
                            })?;
                            Ok(ast_allocator.literal_int(value))
                        }
                        Rule::doubleNumber => {
                            let value = f64::from_str(text).map_err(|source| {
                                ParseError::FloatParseError {
                                    text: text.to_string(),
                                    source,
                                }
                            })?;
                            Ok(ast_allocator.literal_double(value))
                        }
                        rule => Err(ParseError::InternalError {
                            message: format!(
                                "expected an intNumber, hexNumber, or doubleNumber, but got {:?}",
                                rule
                            ),
                        }),
                    }
                }
                Rule::identifier => Ok(ast_allocator.identifier(primary.as_str())),
                Rule::expression => parse_expression(ast_allocator, primary),
                Rule::bool => {
                    let value = primary.as_str().parse().map_err(|source| {
                        ParseError::BooleanParseError {
                            text: primary.as_str().to_owned(),
                            source,
                        }
                    })?;
                    Ok(ast_allocator.literal_bool(value))
                }
                Rule::functionCall => parse_function_call(ast_allocator, primary),
                rule => Err(ParseError::InternalError {
                    message: format!(
                        "number, identifier, expression, bool, or functionCall, but found {:?}",
                        rule
                    ),
                }),
            }
        })
        .map_prefix(|prefix, operand| -> ParseResult<_> {
            let operand = operand?;
            match prefix.as_rule() {
                Rule::neg => Ok(ast_allocator.unary(UnaryOperator::Neg, operand)),
                Rule::not => Ok(ast_allocator.unary(UnaryOperator::Not, operand)),
                Rule::bitwise_not => Ok(ast_allocator.unary(UnaryOperator::BitwiseNot, operand)),
                rule => Err(ParseError::InternalError {
                    message: format!("expected neg, not, or bitwise_not, but found {:?}", rule),
                }),
            }
        })
        .map_infix(|left, op, right| -> ParseResult<_> {
            let left = left?;
            let right = right?;
            match op.as_rule() {
                Rule::add => Ok(ast_allocator.binary(BinaryOperator::Add, left, right)),
                Rule::mul => Ok(ast_allocator.binary(BinaryOperator::Mul, left, right)),
                Rule::sub => Ok(ast_allocator.binary(BinaryOperator::Sub, left, right)),
                Rule::div => Ok(ast_allocator.binary(BinaryOperator::Div, left, right)),
                Rule::rem => Ok(ast_allocator.binary(BinaryOperator::Rem, left, right)),
                Rule::exp => Ok(ast_allocator.binary(BinaryOperator::Exp, left, right)),
                Rule::eq => Ok(ast_allocator.binary(BinaryOperator::Eq, left, right)),
                Rule::neq => Ok(ast_allocator.binary(BinaryOperator::Neq, left, right)),
                Rule::lt => Ok(ast_allocator.binary(BinaryOperator::Lt, left, right)),
                Rule::lte => Ok(ast_allocator.binary(BinaryOperator::Lte, left, right)),
                Rule::gt => Ok(ast_allocator.binary(BinaryOperator::Gt, left, right)),
                Rule::gte => Ok(ast_allocator.binary(BinaryOperator::Gte, left, right)),
                Rule::and => Ok(ast_allocator.binary(BinaryOperator::And, left, right)),
                Rule::or => Ok(ast_allocator.binary(BinaryOperator::Or, left, right)),
                Rule::bitwise_and => {
                    Ok(ast_allocator.binary(BinaryOperator::BitwiseAnd, left, right))
                }
                Rule::bitwise_or => {
                    Ok(ast_allocator.binary(BinaryOperator::BitwiseOr, left, right))
                }
                Rule::bitwise_xor => {
                    Ok(ast_allocator.binary(BinaryOperator::BitwiseXor, left, right))
                }
                Rule::bitwise_shl => {
                    Ok(ast_allocator.binary(BinaryOperator::BitwiseShl, left, right))
                }
                Rule::bitwise_shr => {
                    Ok(ast_allocator.binary(BinaryOperator::BitwiseShr, left, right))
                }
                rule => Err(ParseError::InternalError {
                    message: format!("expected binary operator, but found {:?}", rule),
                }),
            }
        })
        .parse(rule.into_inner())
}

fn parse_function_call<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Expression<'a, PhaseParsed<'a>>> {
    let mut inner = rule.into_inner();
    let name = inner
        .next()
        .ok_or_else(|| ParseError::InternalError {
            message: "expected callee name in function call".to_owned(),
        })?
        .as_str();

    let mut args = ast_allocator.function_call_arguments();
    let args_rule = inner.next().ok_or_else(|| ParseError::InternalError {
        message: "expected call arguments in function call".to_owned(),
    })?;

    for arg in args_rule.into_inner() {
        args.push(parse_expression(ast_allocator, arg)?);
    }

    Ok(ast_allocator.function_call(name, args))
}

fn parse_let_statement<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Statement<'a, PhaseParsed<'a>>> {
    let mut iter = rule.into_inner();
    let mut initializers = ast_allocator.statement_let_initializers();
    loop {
        let Some(initializer_rule) = iter.next() else {
            break;
        };
        let mut initializer_rule = initializer_rule.into_inner();

        let id = initializer_rule
            .next()
            .ok_or_else(|| ParseError::InternalError {
                message: "expected variable identifier in let statement".to_owned(),
            })?;
        let id = intern_string(id.as_str());

        let value = initializer_rule
            .next()
            .ok_or_else(|| ParseError::InternalError {
                message: "expected variable value in let statement".to_owned(),
            })?;
        let value = parse_expression(ast_allocator, value)?;

        initializers.push(LetInitializer {
            variable: id,
            value,
        })
    }
    Ok(ast_allocator.statement_let(initializers))
}

struct ParsedIfComponents<'a> {
    condition: &'a Expression<'a, PhaseParsed<'a>>,
    then_block: &'a Block<'a, PhaseParsed<'a>>,
    else_block: Option<&'a IfElseBlock<'a, PhaseParsed<'a>>>,
}

fn parse_if_components<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<ParsedIfComponents<'a>> {
    let mut inner = rule.into_inner();
    let condition = parse_expression(
        ast_allocator,
        inner.next().ok_or_else(|| ParseError::InternalError {
            message: "expected if condition in if statement".to_owned(),
        })?,
    )?;
    let then_block = parse_block(
        ast_allocator,
        inner.next().ok_or_else(|| ParseError::InternalError {
            message: "expected then block in if statement".to_owned(),
        })?,
    )?;

    let else_block = if let Some(else_part) = inner.next() {
        match else_part.as_rule() {
            Rule::block => {
                Some(ast_allocator.if_else_block(parse_block(ast_allocator, else_part)?))
            }
            Rule::ifStatement => Some(parse_if_else_recursive(ast_allocator, else_part)?),
            rule => {
                return Err(ParseError::InternalError {
                    message: format!("expected block or ifStatement, but found {:?}", rule),
                });
            }
        }
    } else {
        None
    };

    Ok(ParsedIfComponents {
        condition,
        then_block,
        else_block,
    })
}

fn parse_if_else_recursive<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a IfElseBlock<'a, PhaseParsed<'a>>> {
    let ParsedIfComponents {
        condition,
        then_block,
        else_block,
    } = parse_if_components(ast_allocator, rule)?;
    Ok(ast_allocator.if_else_if(condition, then_block, else_block))
}

fn parse_if_statement<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Statement<'a, PhaseParsed<'a>>> {
    let ParsedIfComponents {
        condition,
        then_block,
        else_block,
    } = parse_if_components(ast_allocator, rule)?;
    Ok(ast_allocator.statement_if(condition, then_block, else_block))
}

fn parse_while_statement<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Statement<'a, PhaseParsed<'a>>> {
    let mut inner = rule.into_inner();
    let condition = parse_expression(
        ast_allocator,
        inner.next().ok_or_else(|| ParseError::InternalError {
            message: "expected while condition in while statement".to_owned(),
        })?,
    )?;
    let body = parse_block(
        ast_allocator,
        inner.next().ok_or_else(|| ParseError::InternalError {
            message: "expected while body in while statement".to_owned(),
        })?,
    )?;
    Ok(ast_allocator.statement_while(condition, body))
}

fn parse_statement<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Statement<'a, PhaseParsed<'a>>> {
    let pair = rule
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::InternalError {
            message: "expected statement in statement rule".to_owned(),
        })?;
    match pair.as_rule() {
        Rule::letStatement => parse_let_statement(ast_allocator, pair),
        Rule::assignmentStatement => {
            let mut inner = pair.into_inner();
            let identifier = inner
                .next()
                .ok_or_else(|| ParseError::InternalError {
                    message: "expected identifier on lhs of assignment in assignment statement"
                        .to_owned(),
                })?
                .as_str();
            let expression = parse_expression(
                ast_allocator,
                inner.next().ok_or_else(|| ParseError::InternalError {
                    message: "expected expression on rhs of assignment in assignment statement"
                        .to_owned(),
                })?,
            )?;
            Ok(ast_allocator.statement_assignment(identifier, expression))
        }
        Rule::returnStatement => {
            let expression = match pair.into_inner().next() {
                Some(p) => Some(parse_expression(ast_allocator, p)?),
                None => None,
            };
            Ok(ast_allocator.statement_return(expression))
        }
        Rule::expression => {
            let expression = parse_expression(ast_allocator, pair)?;
            Ok(ast_allocator.statement_expression(expression))
        }
        Rule::ifStatement => parse_if_statement(ast_allocator, pair),
        Rule::whileStatement => parse_while_statement(ast_allocator, pair),
        Rule::breakStatement => Ok(ast_allocator.statement_break()),
        Rule::continueStatement => Ok(ast_allocator.statement_continue()),
        rule => Err(ParseError::InternalError {
            message: format!(
                "expected letStatement, assignmentStatement, returnStatement, expression, ifStatement, whileStatement, breakStatement, or continueStatement, but found {:?}",
                rule
            ),
        }),
    }
}

fn parse_block<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Block<'a, PhaseParsed<'a>>> {
    // We want a parent block to have a smaller id than any nested block,
    // so we generate the block_id first and then recurse.
    let block_id = ast_allocator.next_block_id();

    let mut statements = ast_allocator.statements();
    for pair in rule.into_inner() {
        match pair.as_rule() {
            Rule::statement => statements.push(parse_statement(ast_allocator, pair)?),
            Rule::block => {
                statements.push(ast_allocator.nested_block(parse_block(ast_allocator, pair)?))
            }
            rule => {
                return Err(ParseError::InternalError {
                    message: format!("expected statement or block, but found {:?}", rule),
                });
            }
        }
    }
    Ok(ast_allocator.block_from_statements(block_id, statements))
}

fn parse_function_declaration_arguments<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<BumpVec<'a, FunctionArgument>> {
    let mut arguments = ast_allocator.function_arguments();

    for arg in rule.into_inner() {
        let mut arg = arg.into_inner();
        let name = arg
            .next()
            .ok_or_else(|| ParseError::InternalError {
                message: "expected argument name in function argument".to_owned(),
            })?
            .as_str();
        let arg_type = arg
            .next()
            .ok_or_else(|| ParseError::InternalError {
                message: "expected argument type in function argument".to_owned(),
            })?
            .as_str();
        arguments.push(FunctionArgument {
            name: intern_string(name),
            argument_type: intern_string(arg_type),
        })
    }

    Ok(arguments)
}

fn parse_function_declaration<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a FunctionDeclaration<'a, PhaseParsed<'a>>> {
    ast_allocator.reset_block_id();

    let mut rule_iter = rule.into_inner();
    let name = rule_iter
        .next()
        .ok_or_else(|| ParseError::InternalError {
            message: "expected function name in function declaration".to_owned(),
        })?
        .as_str();

    let arguments_rule = rule_iter.next().ok_or_else(|| ParseError::InternalError {
        message: "expected function arguments in function declaration".to_owned(),
    })?;
    let arguments = parse_function_declaration_arguments(ast_allocator, arguments_rule)?;

    let next = rule_iter.next().ok_or_else(|| ParseError::InternalError {
        message: "expected function return type or body in function declaration".to_owned(),
    })?;
    let (return_type, body_rule) = if let Rule::functionReturnType = next.as_rule() {
        let return_type = next
            .into_inner()
            .next()
            .ok_or_else(|| ParseError::InternalError {
                message: "expected return type in function return type".to_owned(),
            })?
            .as_str();
        (
            Some(intern_string(return_type)),
            rule_iter.next().ok_or_else(|| ParseError::InternalError {
                message: "expected function body in function declaration".to_owned(),
            })?,
        )
    } else {
        (None, next)
    };

    let body = parse_block(ast_allocator, body_rule)?;

    if rule_iter.next().is_some() {
        return Err(ParseError::InternalError {
            message: "unexpected extra elements in function declaration".to_owned(),
        });
    }

    Ok(ast_allocator.function_declaration(name, return_type, arguments, body))
}

fn parse_module<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    module_name: &str,
    rule: Pair<'_, Rule>,
) -> ParseResult<&'a Module<'a, PhaseParsed<'a>>> {
    let mut functions = ast_allocator.functions();
    let mut function_signatures = FunctionSignaturesByName::default();

    let rule_inner = rule.into_inner();
    for inner in rule_inner.into_iter() {
        match inner.as_rule() {
            Rule::EOI => continue,
            Rule::functionDeclaration => {
                let fun = parse_function_declaration(ast_allocator, inner)?;
                function_signatures.insert(fun.signature.name, fun.signature);
                functions.push(fun);
            }
            rule => {
                return Err(ParseError::InternalError {
                    message: format!("expected functionDeclaration or EOI, but found {:?}", rule),
                });
            }
        }
    }

    Ok(ast_allocator.module(module_name, functions, function_signatures))
}

pub fn parse<'a>(
    ast_allocator: &'a ParsedAstAllocator,
    module_name: &str,
    text: &str,
) -> ParseResult<&'a Module<'a, PhaseParsed<'a>>> {
    let pairs = Grammar::parse(Rule::module, text).map_err(Box::new)?;
    let pair = pairs
        .into_iter()
        .next()
        .ok_or_else(|| ParseError::InternalError {
            message: "expected module in input text".to_owned(),
        })?;
    parse_module(ast_allocator, module_name, pair)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_as_expression<'a>(
        ast_allocator: &'a ParsedAstAllocator,
        text: &str,
    ) -> &'a Expression<'a, PhaseParsed<'a>> {
        let pair = Grammar::parse(Rule::expression, text)
            .expect("expression")
            .next()
            .expect("expression pair");
        parse_expression(ast_allocator, pair).expect("parse expression")
    }

    fn parse_as_block<'a>(
        ast_allocator: &'a ParsedAstAllocator,
        text: &str,
    ) -> &'a Block<'a, PhaseParsed<'a>> {
        let pair = Grammar::parse(Rule::block, text)
            .expect("block")
            .next()
            .expect("block pair");
        parse_block(ast_allocator, pair).expect("parse block")
    }

    /// Generates a test case to verify the AST produced by a given source expression.
    /// The AST is passed as its string representation.
    /// The macro allows us to one-line a test case, reducing noise such as the
    /// `#[test]` annotation and the various newline required by a function.
    macro_rules! test_expression {
        ($name: ident, $source: expr, $ast: expr) => {
            #[test]
            fn $name() {
                let ast_allocator = ParsedAstAllocator::default();
                let expression = parse_as_expression(&ast_allocator, $source);
                assert_eq!(expression.to_string(), $ast);
            }
        };
    }

    macro_rules! test_block {
        ($name: ident, $source: expr, $ast: expr) => {
            #[test]
            fn $name() {
                let ast_allocator = ParsedAstAllocator::default();
                let block = parse_as_block(&ast_allocator, $source);
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

    test_expression!(bool_1, "true", "true");
    test_expression!(bool_2, "false", "false");

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

    test_expression!(function_call_no_args, "foo()", "foo()");
    test_expression!(function_call_one_arg, "foo(1)", "foo(1i)");
    test_expression!(
        function_call_multiple_args,
        "foo(1, 2, 3)",
        "foo(1i, 2i, 3i)"
    );

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
        statement_let_multiple_initializers,
        r"{
   let a = 1, b = false;
}",
        r"{ #0
let a = 1i, b = false;
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

    test_block!(
        statement_if_simple,
        r"{
    if true {
        x = 1;
    }
}",
        r"{ #0
if true { #1
x = 1i;
}
}"
    );

    test_block!(
        statement_if_with_else,
        r"{
    if x > 0 {
        y = 1;
    } else {
        y = 0;
    }
}",
        r"{ #0
if (> x 0i) { #1
y = 1i;
} else { #2
y = 0i;
}
}"
    );

    test_block!(
        statement_if_with_else_if,
        r"{
    if x > 0 {
        y = 1;
    } else if x < 0 {
        y = -1;
    } else {
        y = 0;
    }
}",
        r"{ #0
if (> x 0i) { #1
y = 1i;
} else if (< x 0i) { #2
y = (- 1i);
} else { #3
y = 0i;
}
}"
    );

    test_block!(
        statement_while_simple,
        r"{
    while x > 0 {
        x = x - 1;
    }
}",
        r"{ #0
while (> x 0i) { #1
x = (- x 1i);
}
}"
    );

    test_block!(
        statement_break_simple,
        r"{
    break;
}",
        r"{ #0
break;
}"
    );

    test_block!(
        statement_continue_simple,
        r"{
    continue;
}",
        r"{ #0
continue;
}"
    );

    test_block!(
        statement_break_continue_in_while,
        r"{
    while x > 0 {
        if x == 5 {
            break;
        }
        if x % 2 == 0 {
            continue;
        }
        x = x - 1;
    }
}",
        r"{ #0
while (> x 0i) { #1
if (== x 5i) { #2
break;
}
if (== (% x 2i) 0i) { #3
continue;
}
x = (- x 1i);
}
}"
    );

    #[test]
    fn module_fn_with_return_type() {
        let ast_allocator = ParsedAstAllocator::default();
        let module = parse(
            &ast_allocator,
            "test",
            r"
fn add(x: int, y: int) -> int {
    return x + y;
}
",
        )
        .expect("parse module");
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
        let ast_allocator = ParsedAstAllocator::default();
        let module = parse(
            &ast_allocator,
            "test",
            r"
fn foo() {}
",
        )
        .expect("parse module");
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

    #[test]
    fn module_multiple_fn_have_independent_block_id() {
        let ast_allocator = ParsedAstAllocator::default();
        let module = parse(
            &ast_allocator,
            "test",
            r"
fn a() {}
fn b() { { } }
",
        )
        .expect("parse module");
        assert_eq!(
            module.to_string(),
            r"module test

fn a(
) -> void
{ #0
}
fn b(
) -> void
{ #0
{ #1
}
}
"
        );
    }

    #[test]
    fn break_continue_ast() {
        let ast_allocator = ParsedAstAllocator::default();
        let module = parse(
            &ast_allocator,
            "test_break_continue",
            r"fn test_while() {
                while x > 0 {
                    if x == 5 {
                        break;
                    }
                    if x % 2 == 0 {
                        continue;
                    }
                    x = x - 1;
                }
            }",
        )
        .expect("parse should succeed");

        assert_eq!(
            module.to_string(),
            r#"module test_break_continue

fn test_while(
) -> void
{ #0
while (> x 0i) { #1
if (== x 5i) { #2
break;
}
if (== (% x 2i) 0i) { #3
continue;
}
x = (- x 1i);
}
}
"#
        );
    }
}
