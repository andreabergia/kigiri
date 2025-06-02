use crate::symbols::{StringId, get_or_create_string, resolve_string_id};
use bumpalo::collections::Vec as BumpVec;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub type FunctionSignaturesByName<'a> = HashMap<StringId, &'a FunctionSignature<'a>>;

#[derive(Debug, PartialEq)]
pub struct Module<'a> {
    pub name: StringId,
    pub functions: BumpVec<'a, &'a FunctionDeclaration<'a>>,
    pub function_signatures: FunctionSignaturesByName<'a>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionDeclaration<'a> {
    pub signature: &'a FunctionSignature<'a>,
    pub body: &'a Block<'a>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionSignature<'a> {
    pub name: StringId,
    pub return_type: Option<StringId>,
    pub arguments: BumpVec<'a, FunctionArgument>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionArgument {
    pub name: StringId,
    pub arg_type: StringId,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct BlockId(pub u32);

#[derive(Debug, PartialEq)]
pub struct Block<'a> {
    pub id: BlockId,
    pub statements: BumpVec<'a, &'a Statement<'a>>,
}

#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    Let {
        initializers: BumpVec<'a, LetInitializer<'a>>,
    },
    Assignment {
        name: StringId,
        expression: &'a Expression<'a>,
    },
    Return {
        expression: Option<&'a Expression<'a>>,
    },
    Expression {
        expression: &'a Expression<'a>,
    },
    NestedBlock {
        block: &'a Block<'a>,
    },
}

#[derive(Debug, PartialEq)]
pub struct LetInitializer<'a> {
    pub name: StringId,
    pub value: &'a Expression<'a>,
}

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

#[derive(Debug, PartialEq, Clone)]
pub enum LiteralValue {
    Integer(i64),
    Double(f64),
    Boolean(bool),
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

impl Display for Module<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "module {}",
            resolve_string_id(self.name).expect("module name")
        )?;
        writeln!(f)?;
        for function in &self.functions {
            write!(f, "{}", function)?;
        }
        Ok(())
    }
}

impl Display for FunctionDeclaration<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "fn {}(",
            resolve_string_id(self.signature.name).expect("function name")
        )?;
        for arg in self.signature.arguments.iter() {
            writeln!(f, "    {},", arg)?;
        }
        writeln!(
            f,
            ") -> {}",
            match self.signature.return_type {
                Some(return_type) => resolve_string_id(return_type).expect("return type"),
                None => "void",
            }
        )?;
        writeln!(f, "{}", self.body)
    }
}

impl Display for FunctionArgument {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {}",
            resolve_string_id(self.name).expect("argument name"),
            resolve_string_id(self.arg_type).expect("argument type")
        )
    }
}

impl BlockId {
    pub fn next(self) -> BlockId {
        BlockId(self.0 + 1)
    }
}

impl Display for Block<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{ #{}", self.id.0)?;
        for statement in &self.statements {
            writeln!(f, "{}", statement)?;
        }
        write!(f, "}}")
    }
}

impl Display for Statement<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Let { initializers } => {
                write!(f, "let ")?;
                let mut first = true;
                for i in initializers.iter() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    let name = resolve_string_id(i.name).expect("invalid let initializer");
                    write!(f, "{} = {}", name, i.value)?;
                    first = false;
                }
                write!(f, ";")
            }
            Statement::Assignment { name, expression } => {
                write!(
                    f,
                    "{} = {};",
                    resolve_string_id(*name).expect("invalid assignment name"),
                    expression
                )
            }
            Statement::Return { expression } => {
                if let Some(expression) = expression {
                    write!(f, "return {};", expression)
                } else {
                    write!(f, "return;")
                }
            }
            Statement::Expression { expression } => {
                write!(f, "{};", expression)
            }
            Statement::NestedBlock { block } => {
                write!(f, "{}", block)
            }
        }
    }
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

impl Display for LiteralValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralValue::Integer(value) => write!(f, "{}i", value),
            LiteralValue::Double(value) => write!(f, "{}d", value),
            LiteralValue::Boolean(value) => write!(f, "{}", value),
        }
    }
}

impl Display for Expression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier { symbol_id } => {
                let symbol = resolve_string_id(*symbol_id).expect("invalid symbol!");
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
    next_block_id: Cell<BlockId>,
}

impl Ast {
    fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    pub fn identifier(&self, symbol: &str) -> &Expression {
        let id = get_or_create_string(symbol);
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

    pub fn statements(&self) -> BumpVec<&Statement> {
        BumpVec::new_in(&self.arena)
    }

    pub fn next_block_id(&self) -> BlockId {
        let block_id = self.next_block_id.get();
        self.next_block_id.set(block_id.next());
        block_id
    }

    pub fn block_from_statements<'s, 'v>(
        &'s self,
        block_id: BlockId,
        statements: BumpVec<'v, &'v Statement>,
    ) -> &'s Block<'s>
    where
        'v: 's,
    {
        self.alloc(Block {
            id: block_id,
            statements,
        })
    }

    pub fn nested_block<'s, 'b>(&'s self, block: &'b Block<'b>) -> &'s Statement<'s>
    where
        'b: 's,
    {
        self.alloc(Statement::NestedBlock { block })
    }

    pub fn statement_expression<'s, 'e>(
        &'s self,
        expression: &'e Expression<'e>,
    ) -> &'s Statement<'s>
    where
        'e: 's,
    {
        self.alloc(Statement::Expression { expression })
    }

    pub fn statement_return<'s, 'e>(
        &'s self,
        expression: Option<&'e Expression<'e>>,
    ) -> &'s Statement<'s>
    where
        'e: 's,
    {
        self.alloc(Statement::Return { expression })
    }

    pub fn statement_let_initializers(&self) -> BumpVec<LetInitializer> {
        BumpVec::new_in(&self.arena)
    }

    pub fn statement_let<'s, 'e>(
        &'s self,
        initializers: BumpVec<'e, LetInitializer<'e>>,
    ) -> &'s Statement<'s>
    where
        'e: 's,
    {
        self.alloc(Statement::Let { initializers })
    }

    pub fn statement_assignment<'s, 'e>(
        &'s self,
        name: &str,
        expression: &'e Expression<'e>,
    ) -> &'s Statement<'s>
    where
        'e: 's,
    {
        self.alloc(Statement::Assignment {
            name: get_or_create_string(name),
            expression,
        })
    }

    pub fn functions(&self) -> BumpVec<&FunctionDeclaration> {
        BumpVec::new_in(&self.arena)
    }

    pub fn module<'s, 'f, 'f2>(
        &'s self,
        module_name: &str,
        functions: BumpVec<'f, &FunctionDeclaration<'f>>,
        function_signatures: FunctionSignaturesByName<'f2>,
    ) -> &'s Module<'s>
    where
        'f: 's,
        'f2: 's,
    {
        let name = get_or_create_string(module_name);
        self.alloc(Module {
            name,
            functions,
            function_signatures,
        })
    }

    pub fn function_arguments(&self) -> BumpVec<FunctionArgument> {
        BumpVec::new_in(&self.arena)
    }

    pub fn function_declaration<'s, 'a, 'b>(
        &'s self,
        name: &str,
        return_type: Option<StringId>,
        arguments: BumpVec<'a, FunctionArgument>,
        body: &'b Block<'b>,
    ) -> &'s FunctionDeclaration<'s>
    where
        'a: 's,
        'b: 's,
    {
        self.alloc(FunctionDeclaration {
            signature: self.alloc(FunctionSignature {
                name: get_or_create_string(name),
                return_type,
                arguments,
            }),
            body,
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

    #[test]
    fn format_block() {
        let ast = Ast::default();

        let block_id = ast.next_block_id();
        let x = ast.identifier("x");
        let statement = ast.statement_expression(x);
        let mut statements = ast.statements();
        statements.push(statement);
        let block = ast.block_from_statements(block_id, statements);

        assert_eq!(
            block.to_string(),
            r"{ #0
x;
}"
        );
    }

    #[test]
    fn format_function() {
        let ast = Ast::default();

        let block_id = ast.next_block_id();
        let x = ast.identifier("x");
        let statements = ast.statements();
        let block = ast.block_from_statements(block_id, statements);

        let mut args = ast.function_arguments();
        args.push(FunctionArgument {
            name: get_or_create_string("x"),
            arg_type: get_or_create_string("int"),
        });
        let fun = ast.function_declaration("foo", None, args, block);

        assert_eq!(
            fun.to_string(),
            r"fn foo(
    x: int,
) -> void
{ #0
}
"
        );
    }
}
