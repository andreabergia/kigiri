use crate::typed_ast::TypedStatement;
use crate::{Type, TypedExpression};
use bumpalo::collections::Vec as BumpVec;
use parser::{BinaryOperator, Expression, Statement, UnaryOperator};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum SemanticAnalysisError {
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
pub struct SemanticAnalyzer {
    arena: bumpalo::Bump,
}

impl SemanticAnalyzer {
    fn analyze_statement<'s>(
        &'s self,
        statement: &parser::Statement,
    ) -> Result<BumpVec<'s, &'s TypedStatement<'s>>, SemanticAnalysisError> {
        match statement {
            Statement::Let { initializers } => {
                // let mut vec = BumpVec::with_capacity_in(initializers.len(), &self.arena);
                // for initializer in initializers {
                //     let
                // }
                todo!()
            }
            Statement::Assignment { name, expression } => {
                todo!()
            }
            Statement::Return { expression } => {
                let value = expression
                    .map(|expr| self.analyze_expression(expr))
                    .transpose()?;

                Ok(self.as_bump_vec(TypedStatement::Return { value }))
            }
            Statement::Expression { expression } => {
                let typed_expression = self.analyze_expression(expression)?;
                Ok(self.as_bump_vec(TypedStatement::Expression {
                    expression: typed_expression,
                }))
            }
            Statement::NestedBlock { block } => {
                todo!()
            }
        }
    }

    pub fn analyze_expression<'s>(
        &'s self,
        expr: &Expression,
    ) -> Result<&'s TypedExpression<'s>, SemanticAnalysisError> {
        match expr {
            Expression::Identifier { symbol_id } => todo!(),

            // Literals will never fail
            Expression::Literal(value) => Ok(self.alloc(TypedExpression::Literal {
                resolved_type: Type::of_literal(value),
                value: value.clone(),
            })),

            // Unary operators - can fail!
            Expression::Unary { operator, operand } => {
                let typed_operand = self.analyze_expression(operand)?;
                let operand_type = typed_operand.resolved_type();
                if (Self::unary_op_is_allowed(operator.clone(), operand_type.clone())) {
                    Ok(self.alloc(TypedExpression::Unary {
                        resolved_type: operand_type.clone(),
                        operator: operator.clone(),
                        operand: typed_operand,
                    }))
                } else {
                    Err(SemanticAnalysisError::CannotApplyUnaryOperatorToType {
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
                let typed_left = self.analyze_expression(left)?;
                let typed_right = self.analyze_expression(right)?;
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
                    Err(SemanticAnalysisError::CannotApplyBinaryOperatorToType {
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

    #[inline]
    fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    fn as_bump_vec<T>(&self, node: T) -> BumpVec<'_, &T> {
        let mut vec = BumpVec::with_capacity_in(1, &self.arena);
        vec.push(self.alloc(node));
        vec
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod expressions {
        use super::*;

        /// Generates a test case to verify the typed AST produced by a given
        /// source expression. The typed AST is passed as its string representation.
        macro_rules! test_ok {
            ($name: ident, $source: expr, $typed_ast: expr) => {
                #[test]
                fn $name() {
                    let ast = parser::Ast::default();
                    let expression = parser::parse_as_expression(&ast, $source);
                    let type_engine = SemanticAnalyzer::default();
                    let result = type_engine.analyze_expression(expression);
                    assert_eq!(
                        result
                            .expect("should have matched types correctly")
                            .to_string(),
                        $typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast = parser::Ast::default();
                    let expression = parser::parse_as_expression(&ast, $source);
                    let type_engine = SemanticAnalyzer::default();
                    let result = type_engine.analyze_expression(expression);
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
                operand_type: Type::Boolean
            }
        );

        test_ko!(
            unary_not_int,
            "! 3",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::Not,
                operand_type: Type::Int
            }
        );
        test_ko!(
            unary_not_double,
            "! 3.14",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::Not,
                operand_type: Type::Double
            }
        );
        test_ok!(unary_not_boolean, "! false", "(!b false)");

        test_ok!(unary_bitwise_not_int, "~ 3", "(~i 3i)");
        test_ko!(
            unary_bitwise_not_double,
            "~ 3.14",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::BitwiseNot,
                operand_type: Type::Double
            }
        );
        test_ko!(
            unary_bitwise_not_boolean,
            "~ false",
            SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                operator: UnaryOperator::BitwiseNot,
                operand_type: Type::Boolean
            }
        );

        test_ok!(binary_add_int, "1 + 2", "(+i 1i 2i)");
        test_ok!(binary_add_double, "1.0 + 2.0", "(+d 1d 2d)");
        test_ko!(
            binary_add_int_double,
            "1 + 3.14",
            SemanticAnalysisError::CannotApplyBinaryOperatorToType {
                operator: BinaryOperator::Add,
                left_type: Type::Int,
                right_type: Type::Double,
            }
        );
    }

    mod statements {
        use super::*;

        #[test]
        fn assign() {
            let ast = parser::Ast::default();
            let expression = parser::parse_as_block(
                &ast,
                r"{
    return 42;
}",
            );
            let type_engine = SemanticAnalyzer::default();
            let result = type_engine.analyze_statement(expression.statements[0]);

            assert_eq!(
                result.expect("should have matched types correctly")[0].to_string(),
                "return 42i"
            );
        }
    }
}
