use crate::memory::{StringId, StringInterner};
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
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

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Identifier {
        string_interner: Rc<RefCell<StringInterner>>,
        symbol_id: StringId,
    },
    LiteralInteger {
        value: i64,
    },
    LiteralDouble {
        value: f64,
    },
    LiteralBoolean {
        value: bool,
    },

    Negate {
        operand: &'a Expression<'a>,
    },
    Not {
        operand: &'a Expression<'a>,
    },

    Add {
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    },
    Sub {
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    },
    Mul {
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    },
    Div {
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    },
    Rem {
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    },
    // FunctionCall(FunctionCall<'input>),
}

impl Display for Expression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier {
                string_interner,
                symbol_id,
            } => {
                let string_interner = string_interner.borrow();
                let symbol = string_interner
                    .resolve(*symbol_id)
                    .expect("invalid symbol!");
                write!(f, "{}", symbol)
            }
            Expression::LiteralInteger { value } => write!(f, "{}i", value),
            Expression::LiteralDouble { value } => write!(f, "{}d", value),
            Expression::LiteralBoolean { value } => write!(f, "{}", value),
            Expression::Negate { operand } => write!(f, "(- {})", operand),
            Expression::Not { operand } => write!(f, "(! {})", operand),
            Expression::Add { left, right } => write!(f, "(+ {} {})", left, right),
            Expression::Sub { left, right } => write!(f, "(- {} {})", left, right),
            Expression::Mul { left, right } => write!(f, "(* {} {})", left, right),
            Expression::Div { left, right } => write!(f, "(/ {} {})", left, right),
            Expression::Rem { left, right } => write!(f, "(% {} {})", left, right),
        }
    }
}

pub struct Ast {
    arena: bumpalo::Bump,
    interner: Rc<RefCell<StringInterner>>,
}

impl Ast {
    pub fn new(interner: Rc<RefCell<StringInterner>>) -> Self {
        Self {
            arena: bumpalo::Bump::new(),
            interner,
        }
    }

    #[cfg(test)]
    pub fn for_tests() -> Self {
        let string_interner = Rc::new(RefCell::new(StringInterner::default()));
        Self::new(string_interner)
    }

    fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    pub fn identifier(&self, symbol: &str) -> &Expression {
        self.alloc(Expression::Identifier {
            string_interner: self.interner.clone(),
            symbol_id: self.interner.borrow_mut().get_or_intern(symbol),
        })
    }

    pub fn literal_integer(&self, value: i64) -> &Expression {
        self.alloc(Expression::LiteralInteger { value })
    }

    pub fn add<'s, 'l, 'r>(
        &'s self,
        left: &'l Expression,
        right: &'r Expression,
    ) -> &'s Expression<'s>
    where
        'l: 's,
        'r: 's,
    {
        self.alloc(Expression::Add { left, right })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_allocate_via_ast() {
        let ast = Ast::for_tests();
        let id = ast.literal_integer(1);
        assert_eq!(id, &Expression::LiteralInteger { value: 1 });
    }

    #[test]
    fn format_expressions() {
        let ast = Ast::for_tests();

        let x = ast.identifier("x");
        let one = ast.literal_integer(1);
        let sum = ast.add(x, one);
        assert_eq!(sum.to_string(), "(+ x 1i)");
    }
}
