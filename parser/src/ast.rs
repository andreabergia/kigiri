use crate::memory::{StringId, StringInterner};
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

#[derive(Debug, PartialEq)]
pub enum Expression<'a, 'i> {
    Identifier {
        string_interner: &'i StringInterner,
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
        operand: &'a Expression<'a, 'i>,
    },
    Not {
        operand: &'a Expression<'a, 'i>,
    },

    Add {
        left: &'a Expression<'a, 'i>,
        right: &'a Expression<'a, 'i>,
    },
    Sub {
        left: &'a Expression<'a, 'i>,
        right: &'a Expression<'a, 'i>,
    },
    Mul {
        left: &'a Expression<'a, 'i>,
        right: &'a Expression<'a, 'i>,
    },
    Div {
        left: &'a Expression<'a, 'i>,
        right: &'a Expression<'a, 'i>,
    },
    Rem {
        left: &'a Expression<'a, 'i>,
        right: &'a Expression<'a, 'i>,
    },
    // FunctionCall(FunctionCall<'input>),
}

impl Display for Expression<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier {
                string_interner,
                symbol_id,
            } => {
                let symbol = string_interner
                    .resolve(*symbol_id)
                    .expect("invalid symbol!");
                write!(f, "{}", symbol)
            }
            Expression::LiteralInteger { value } => write!(f, "{}i", value),
            Expression::LiteralDouble { value } => write!(f, "{}d", value),
            Expression::LiteralBoolean { value } => write!(f, "{}", value.to_string()),
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

pub struct Ast<'interner> {
    string_interner: &'interner mut StringInterner,
    arena: bumpalo::Bump,
}

impl<'interner> Ast<'interner> {
    pub fn new(string_interner: &'interner mut StringInterner) -> Self {
        Self {
            string_interner,
            arena: bumpalo::Bump::new(),
        }
    }

    pub fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    fn symbol_for(&mut self, string: &str) -> StringId {
        self.string_interner.get_or_intern(string)
    }

    pub fn identifier<'s>(&'s mut self, string: &str) -> &'s Expression<'s, 'interner>
    where
        's: 'interner,
    {
        let symbol = self.symbol_for(string);
        self.alloc(Expression::Identifier {
            string_interner: self.string_interner,
            symbol_id: symbol,
        })
    }

    pub fn literal_integer(&self, value: i64) -> &Expression<'_, 'interner> {
        self.alloc(Expression::LiteralInteger { value })
    }

    pub fn add<'s>(
        &'s self,
        left: &'s Expression<'s, 'interner>,
        right: &'s Expression<'s, 'interner>,
    ) -> &'s Expression<'s, 'interner> {
        self.alloc(Expression::Add { left, right })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_allocate_via_ast() {
        let mut string_interner = StringInterner::default();
        let ast = Ast::new(&mut string_interner);
        let id = ast.alloc(Expression::LiteralInteger { value: 1 });
        assert_eq!(id, &Expression::LiteralInteger { value: 1 });
    }

    #[test]
    fn format_expressions() {
        let mut string_interner = StringInterner::default();
        let mut ast = Ast::new(&mut string_interner);

        let x = ast.identifier("x");
        let one = ast.literal_integer(1);
        let sum = ast.add(x, one);
        assert_eq!(sum.to_string(), "(+ x 1i)");
    }
}
