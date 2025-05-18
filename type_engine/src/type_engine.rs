use crate::{Type, TypedExpression};
use parser::{BinaryOperator, Expression, UnaryOperator};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum TypeEngineError {
    #[error("cannot apply operator {operator} to type {operand_type}")]
    CannotApplyUnaryOperatorToType {
        operator: UnaryOperator,
        operand_type: Type,
    },
    #[error("cannot apply operator {operator} to types {left_type} and {right_type}")]
    CannotApplyBinaryOperatorToType {
        operator: BinaryOperator,
        left_type: Type,
        right_type: Type,
    },
}

#[derive(Default)]
pub struct TypeEngine {
    arena: bumpalo::Bump,
}

impl TypeEngine {
    pub fn check_and_infer_types<'s>(
        &'s self,
        root: &Expression,
    ) -> Result<&'s TypedExpression<'s>, TypeEngineError> {
        match root {
            Expression::Identifier { symbol_id } => todo!(),

            // Literals will never fail
            Expression::Literal(value) => Ok(self.alloc(TypedExpression::Literal {
                resolved_type: Type::of_literal(value),
                value: value.clone(),
            })),

            // Unary operators - can fail!
            Expression::Unary { operator, operand } => {
                let typed_operand = self.check_and_infer_types(operand)?;
                let operand_type = typed_operand.resolved_type();
                if (Self::unary_op_is_allowed(operator.clone(), operand_type.clone())) {
                    Ok(self.alloc(TypedExpression::Unary {
                        resolved_type: operand_type.clone(),
                        operator: operator.clone(),
                        operand: typed_operand,
                    }))
                } else {
                    Err(TypeEngineError::CannotApplyUnaryOperatorToType {
                        operator: operator.clone(),
                        operand_type: operand_type.clone(),
                    })
                }
            }

            // Binary operators - can fail!
            Expression::Binary {
                operator,
                left,
                right,
            } => {
                let typed_left = self.check_and_infer_types(left)?;
                let typed_right = self.check_and_infer_types(right)?;
                let left_type = typed_left.resolved_type();
                let right_type = typed_right.resolved_type();
                if Self::bin_op_is_allowed(operator.clone(), left_type.clone(), right_type.clone())
                {
                    Ok(self.alloc(TypedExpression::Binary {
                        resolved_type: left_type.clone(),
                        operator: operator.clone(),
                        left: typed_left,
                        right: typed_right,
                    }))
                } else {
                    Err(TypeEngineError::CannotApplyBinaryOperatorToType {
                        operator: operator.clone(),
                        left_type: left_type.clone(),
                        right_type: right_type.clone(),
                    })
                }
            }
        }
    }

    fn unary_op_is_allowed(operator: UnaryOperator, operand_type: Type) -> bool {
        match operator {
            UnaryOperator::Neg => operand_type == Type::Int || operand_type == Type::Double,
            UnaryOperator::Not => operand_type == Type::Boolean,
            UnaryOperator::BitwiseNot => operand_type == Type::Int,
        }
    }

    fn bin_op_is_allowed(operator: BinaryOperator, left_type: Type, right_type: Type) -> bool {
        match operator {
            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Exp => {
                left_type == right_type && (left_type == Type::Int || left_type == Type::Double)
            }
            BinaryOperator::Rem => left_type == right_type && left_type == Type::Int,
            BinaryOperator::Eq | BinaryOperator::Neq => true,
            BinaryOperator::Lt | BinaryOperator::Lte | BinaryOperator::Gt | BinaryOperator::Gte => {
                left_type == right_type && (left_type == Type::Int || left_type == Type::Double)
            }
            BinaryOperator::And | BinaryOperator::Or => {
                left_type == right_type && left_type == Type::Boolean
            }
            BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseOr
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseShl
            | BinaryOperator::BitwiseShr => left_type == right_type && left_type == Type::Int,
        }
    }

    fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Generates a test case to verify the typed AST produced by a given
    /// source expression. The typed AST is passed as its string representation.
    macro_rules! test_types_ok {
        ($name: ident, $source: expr, $typed_ast: expr) => {
            #[test]
            fn $name() {
                let ast = parser::Ast::default();
                let expression = parser::parse(&ast, $source);
                let type_engine = TypeEngine::default();
                let result = type_engine.check_and_infer_types(expression);
                assert_eq!(
                    result
                        .expect("should have matched types correctly")
                        .to_string(),
                    $typed_ast
                );
            }
        };
    }

    macro_rules! test_types_ko {
        ($name: ident, $source: expr, $expected_error: expr) => {
            #[test]
            fn $name() {
                let ast = parser::Ast::default();
                let expression = parser::parse(&ast, $source);
                let type_engine = TypeEngine::default();
                let result = type_engine.check_and_infer_types(expression);
                assert_eq!(
                    result.expect_err("should have failed to match types"),
                    $expected_error
                );
            }
        };
    }

    // Literals

    test_types_ok!(literal_int, "1", "1i");
    test_types_ok!(literal_double, "3.14", "3.14d");
    test_types_ok!(literal_boolean, "true", "true");

    // Unary

    test_types_ok!(unary_neg_int, "- 3", "(-i 3i)");
    test_types_ok!(unary_neg_double, "- 3.14", "(-d 3.14d)");
    test_types_ko!(
        unary_neg_boolean,
        "- false",
        TypeEngineError::CannotApplyUnaryOperatorToType {
            operator: UnaryOperator::Neg,
            operand_type: Type::Boolean
        }
    );

    test_types_ko!(
        unary_not_int,
        "! 3",
        TypeEngineError::CannotApplyUnaryOperatorToType {
            operator: UnaryOperator::Not,
            operand_type: Type::Int
        }
    );
    test_types_ko!(
        unary_not_double,
        "! 3.14",
        TypeEngineError::CannotApplyUnaryOperatorToType {
            operator: UnaryOperator::Not,
            operand_type: Type::Double
        }
    );
    test_types_ok!(unary_not_boolean, "! false", "(!b false)");

    test_types_ok!(unary_bitwise_not_int, "~ 3", "(~i 3i)");
    test_types_ko!(
        unary_bitwise_not_double,
        "~ 3.14",
        TypeEngineError::CannotApplyUnaryOperatorToType {
            operator: UnaryOperator::BitwiseNot,
            operand_type: Type::Double
        }
    );
    test_types_ko!(
        unary_bitwise_not_boolean,
        "~ false",
        TypeEngineError::CannotApplyUnaryOperatorToType {
            operator: UnaryOperator::BitwiseNot,
            operand_type: Type::Boolean
        }
    );

    test_types_ok!(binary_add_int, "1 + 2", "(+i 1i 2i)");
    test_types_ok!(binary_add_double, "1.0 + 2.0", "(+d 1d 2d)");
    test_types_ko!(
        binary_add_int_double,
        "1 + 3.14",
        TypeEngineError::CannotApplyBinaryOperatorToType {
            operator: BinaryOperator::Add,
            left_type: Type::Int,
            right_type: Type::Double,
        }
    );
    // TODO: more test cases
}
