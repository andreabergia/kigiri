use crate::memory::{STRING_INTERNER, StringId};
use std::fmt::{Display, Formatter};
//
//
// #[derive(Debug, PartialEq)]
// pub struct Function<'input> {
//     pub name: &'input str,
//     pub args: Vec<&'input str>,
//     pub block: Block<'input>,
// }
//
// pub type Program<'input> = Vec<Function<'input>>;
//
// #[derive(Debug, PartialEq)]
// pub enum BlockElement<'input> {
//     LetStatement {
//         name: &'input str,
//         expression: Expression<'input>,
//     },
//     AssignmentStatement {
//         name: &'input str,
//         expression: Expression<'input>,
//     },
//     ReturnStatement(Expression<'input>),
//     NestedBlock(Block<'input>),
// }
//
// pub type Block<'input> = Vec<BlockElement<'input>>;
//
// #[derive(Debug, PartialEq)]
// pub struct FunctionCall<'input> {
//     pub name: &'input str,
//     pub args: Vec<Expression<'input>>,
// }

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryOperator {
    Neg,
    Not,
    BitwiseNot,
}

impl UnaryOperator {
    pub fn name(&self) -> &'static str {
        match self {
            UnaryOperator::Neg => "neg",
            UnaryOperator::Not => "not",
            UnaryOperator::BitwiseNot => "bitwise_not",
        }
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                UnaryOperator::Neg => "-",
                UnaryOperator::Not => "!",
                UnaryOperator::BitwiseNot => "~",
            }
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Exp,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitwiseShl,
    BitwiseShr,
}

impl BinaryOperator {
    pub fn name(&self) -> &'static str {
        match self {
            BinaryOperator::Add => "add",
            BinaryOperator::Sub => "sub",
            BinaryOperator::Mul => "mul",
            BinaryOperator::Div => "div",
            BinaryOperator::Rem => "rem",
            BinaryOperator::Exp => "exp",
            BinaryOperator::Eq => "eq",
            BinaryOperator::Neq => "neq",
            BinaryOperator::Lt => "lt",
            BinaryOperator::Lte => "lte",
            BinaryOperator::Gt => "gt",
            BinaryOperator::Gte => "gte",
            BinaryOperator::And => "and",
            BinaryOperator::Or => "or",
            BinaryOperator::BitwiseAnd => "bitwise_and",
            BinaryOperator::BitwiseOr => "bitwise_or",
            BinaryOperator::BitwiseXor => "bitwise_xor",
            BinaryOperator::BitwiseShl => "bitwise_shl",
            BinaryOperator::BitwiseShr => "bitwise_shr",
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                BinaryOperator::Add => "+",
                BinaryOperator::Sub => "-",
                BinaryOperator::Mul => "*",
                BinaryOperator::Div => "/",
                BinaryOperator::Rem => "%",
                BinaryOperator::Exp => "**",
                BinaryOperator::Eq => "==",
                BinaryOperator::Neq => "!=",
                BinaryOperator::Lt => "<",
                BinaryOperator::Lte => "<=",
                BinaryOperator::Gt => ">",
                BinaryOperator::Gte => ">=",
                BinaryOperator::And => "&&",
                BinaryOperator::Or => "||",
                BinaryOperator::BitwiseAnd => "&",
                BinaryOperator::BitwiseOr => "|",
                BinaryOperator::BitwiseXor => "^",
                BinaryOperator::BitwiseShl => "<<",
                BinaryOperator::BitwiseShr => ">>",
            }
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum LiteralValue {
    Integer(i64),
    Double(f64),
    Boolean(bool),
}

impl Display for LiteralValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralValue::Integer(value) => write!(f, "{}i", value),
            LiteralValue::Double(value) => write!(f, "{}d", value),
            LiteralValue::Boolean(value) => write!(f, "{}", value),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Identifier {
        symbol_id: StringId,
    },
    Literal(LiteralValue),
    Unary {
        operator: UnaryOperator,
        operand: &'a Expression<'a>,
    },
    Binary {
        operator: BinaryOperator,
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    },
    // FunctionCall(FunctionCall<'input>),
}

impl Display for Expression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier { symbol_id } => {
                let interner = STRING_INTERNER
                    .lock()
                    .expect("should be able to mutate the string interner");
                let symbol = interner.resolve(*symbol_id).expect("invalid symbol!");
                write!(f, "{}", symbol)
            }
            Expression::Literal(value) => write!(f, "{}", value),
            Expression::Unary { operator, operand } => write!(f, "({} {})", operator, operand),
            Expression::Binary {
                operator,
                left,
                right,
            } => write!(f, "({} {} {})", operator, left, right),
        }
    }
}

#[derive(Default)]
pub struct Ast {
    arena: bumpalo::Bump,
}

impl Ast {
    fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    pub fn identifier(&self, symbol: &str) -> &Expression {
        let mut interner = STRING_INTERNER
            .lock()
            .expect("should be able to lock the interner");
        let id = interner.get_or_intern(symbol);
        self.alloc(Expression::Identifier { symbol_id: id })
    }

    pub fn literal_integer(&self, value: i64) -> &Expression {
        self.alloc(Expression::Literal(LiteralValue::Integer(value)))
    }

    pub fn literal_double(&self, value: f64) -> &Expression {
        self.alloc(Expression::Literal(LiteralValue::Double(value)))
    }

    pub fn literal_boolean(&self, value: bool) -> &Expression {
        self.alloc(Expression::Literal(LiteralValue::Boolean(value)))
    }

    pub fn unary<'s, 'l, 'r>(
        &'s self,
        operator: UnaryOperator,
        operand: &'l Expression,
    ) -> &'s Expression<'s>
    where
        'l: 's,
        'r: 's,
    {
        self.alloc(Expression::Unary { operator, operand })
    }

    pub fn binary<'s, 'l, 'r>(
        &'s self,
        operator: BinaryOperator,
        left: &'l Expression,
        right: &'r Expression,
    ) -> &'s Expression<'s>
    where
        'l: 's,
        'r: 's,
    {
        self.alloc(Expression::Binary {
            operator,
            left,
            right,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_allocate_via_ast() {
        let ast = Ast::default();
        let id = ast.literal_integer(1);
        assert_eq!(id, &Expression::Literal(LiteralValue::Integer(1)));
    }

    #[test]
    fn format_expressions() {
        let ast = Ast::default();

        let x = ast.identifier("x");
        let one = ast.literal_integer(1);
        let sum = ast.binary(BinaryOperator::Add, x, one);
        let two = ast.literal_double(2.1);
        let neg = ast.unary(UnaryOperator::Neg, two);
        let mul = ast.binary(BinaryOperator::Mul, sum, neg);
        let lt = ast.binary(BinaryOperator::Lt, mul, ast.literal_double(4.2));
        let true_lit = ast.literal_boolean(true);
        let or = ast.binary(BinaryOperator::Or, lt, true_lit);
        assert_eq!(or.to_string(), "(|| (< (* (+ x 1i) (- 2.1d)) 4.2d) true)");
    }
}
