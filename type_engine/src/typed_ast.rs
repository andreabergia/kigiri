use crate::types::Type;
use parser::{BinaryOperator, LiteralValue, UnaryOperator};
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
pub enum TypedExpression<'a> {
    // TODO
    // Identifier {
    //     resolved_type: Type,
    //     string_interner: Rc<RefCell<StringInterner>>,
    //     symbol_id: StringId,
    // },
    Literal {
        resolved_type: Type,
        value: LiteralValue,
    },
    Unary {
        resolved_type: Type,
        operator: UnaryOperator,
        operand: &'a TypedExpression<'a>,
    },
    Binary {
        resolved_type: Type,
        operator: BinaryOperator,
        left: &'a TypedExpression<'a>,
        right: &'a TypedExpression<'a>,
    },
}

impl Display for TypedExpression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            // Expression::Identifier {
            //     string_interner,
            //     symbol_id,
            // } => {
            //     let string_interner = string_interner.borrow();
            //     let symbol = string_interner
            //         .resolve(*symbol_id)
            //         .expect("invalid symbol!");
            //     write!(f, "{}", symbol)
            // }
            TypedExpression::Literal { value, .. } => write!(f, "{}", value),
            TypedExpression::Unary {
                resolved_type,
                operator,
                operand,
            } => write!(
                f,
                "({}{} {})",
                operator,
                resolved_type.to_string_short(),
                operand
            ),
            TypedExpression::Binary {
                resolved_type,
                operator,
                left,
                right,
            } => write!(
                f,
                "({}{} {} {})",
                operator,
                resolved_type.to_string_short(),
                left,
                right
            ),
        }
    }
}

impl<'a> TypedExpression<'a> {
    pub fn resolved_type(&self) -> Type {
        match self {
            // Expression::Identifier { resolved_type, .. } => *resolved_type,
            TypedExpression::Literal { resolved_type, .. } => resolved_type.clone(),
            TypedExpression::Unary { resolved_type, .. } => resolved_type.clone(),
            TypedExpression::Binary { resolved_type, .. } => resolved_type.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_contains_type_after_operator() {
        let typed_expression = TypedExpression::Binary {
            resolved_type: Type::Int,
            operator: BinaryOperator::Add,
            left: &TypedExpression::Literal {
                resolved_type: Type::Int,
                value: LiteralValue::Integer(1),
            },
            right: &TypedExpression::Literal {
                resolved_type: Type::Int,
                value: LiteralValue::Integer(2),
            },
        };
        assert_eq!(format!("{}", typed_expression), "(+i 1i 2i)");
    }
}
