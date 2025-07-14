use crate::FunctionSignaturesByName;
use crate::parsed_ast::PhaseParsed;
use crate::symbols::{StringId, intern_string, resolve_string_id};
use bumpalo::collections::Vec as BumpVec;
use std::cell::Cell;
use std::fmt::{Debug, Display, Formatter};

pub trait CompilationPhase {
    type SymbolTableType: Debug + PartialEq;
    type FunctionArgumentType: Debug + PartialEq;
    type ExpressionType: Debug + PartialEq;
    type UnaryBinaryOperandType: Debug + PartialEq;
    type IdentifierType: Debug + PartialEq;
    type FunctionReturnType: Debug + PartialEq;
    type FunctionCallReturnType: Debug + PartialEq;
}

#[derive(Debug, PartialEq)]
pub struct Module<'a, Phase: CompilationPhase> {
    pub name: StringId,
    pub functions: BumpVec<'a, &'a FunctionDeclaration<'a, Phase>>,
    pub function_signatures: FunctionSignaturesByName<'a, Phase>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionDeclaration<'a, Phase: CompilationPhase> {
    pub signature: &'a FunctionSignature<'a, Phase>,
    pub body: &'a Block<'a, Phase>,
    pub symbol_table: <Phase as CompilationPhase>::SymbolTableType,
}

#[derive(Debug, PartialEq)]
pub struct FunctionSignature<'a, Phase: CompilationPhase> {
    pub name: StringId,
    pub return_type: Option<<Phase as CompilationPhase>::FunctionReturnType>,
    pub arguments: BumpVec<'a, <Phase as CompilationPhase>::FunctionArgumentType>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionArgument {
    pub name: StringId,
    pub arg_type: StringId,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct BlockId(pub u32);

#[derive(Debug, PartialEq)]
pub struct Block<'a, Phase: CompilationPhase> {
    pub id: BlockId,
    pub statements: BumpVec<'a, &'a Statement<'a, Phase>>,
    pub symbol_table: <Phase as CompilationPhase>::SymbolTableType,
}

#[derive(Debug, PartialEq)]
pub enum Statement<'a, Phase: CompilationPhase> {
    Let {
        initializers: BumpVec<'a, LetInitializer<'a, Phase>>,
    },
    Assignment {
        target: <Phase as CompilationPhase>::IdentifierType,
        expression: &'a Expression<'a, Phase>,
    },
    Return {
        expression: Option<&'a Expression<'a, Phase>>,
    },
    Expression {
        expression: &'a Expression<'a, Phase>,
    },
    NestedBlock {
        block: &'a Block<'a, Phase>,
    },
}

#[derive(Debug, PartialEq)]
pub struct LetInitializer<'a, Phase: CompilationPhase> {
    pub variable: <Phase as CompilationPhase>::IdentifierType,
    pub value: &'a Expression<'a, Phase>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionCall<'a, Phase: CompilationPhase> {
    pub name: StringId,
    pub args: BumpVec<'a, &'a Expression<'a, Phase>>,
}

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
pub enum Expression<'a, Phase: CompilationPhase> {
    Identifier {
        resolved_type: Phase::ExpressionType,
        name: Phase::IdentifierType,
    },
    Literal {
        resolved_type: Phase::ExpressionType,
        value: LiteralValue,
    },
    Unary {
        resolved_type: Phase::UnaryBinaryOperandType,
        operator: UnaryOperator,
        operand: &'a Expression<'a, Phase>,
    },
    Binary {
        result_type: Phase::UnaryBinaryOperandType,
        operator: BinaryOperator,
        operand_type: Phase::UnaryBinaryOperandType,
        left: &'a Expression<'a, Phase>,
        right: &'a Expression<'a, Phase>,
    },
    FunctionCall {
        name: Phase::IdentifierType,
        args: BumpVec<'a, &'a Expression<'a, Phase>>,
        return_type: Phase::FunctionCallReturnType,
    },
}

impl<'f, Phase: CompilationPhase> Display for Module<'f, Phase>
where
    FunctionDeclaration<'f, Phase>: Display,
{
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

impl Display for FunctionDeclaration<'_, PhaseParsed<'_>> {
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
            match &self.signature.return_type {
                Some(return_type) => resolve_string_id(*return_type).expect("return type"),
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

impl Display for Block<'_, PhaseParsed<'_>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{ #{}", self.id.0)?;
        for statement in &self.statements {
            writeln!(f, "{}", statement)?;
        }
        write!(f, "}}")
    }
}

impl Display for Statement<'_, PhaseParsed<'_>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Let { initializers } => {
                write!(f, "let ")?;
                let mut first = true;
                for i in initializers.iter() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    let name = resolve_string_id(i.variable).expect("invalid let initializer");
                    write!(f, "{} = {}", name, i.value)?;
                    first = false;
                }
                write!(f, ";")
            }
            Statement::Assignment { target, expression } => {
                write!(
                    f,
                    "{} = {};",
                    resolve_string_id(*target).expect("invalid assignment name"),
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

impl Display for Expression<'_, PhaseParsed<'_>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier { name, .. } => {
                let symbol = resolve_string_id(*name).expect("invalid symbol!");
                write!(f, "{}", symbol)
            }
            Expression::Literal { value, .. } => write!(f, "{}", value),
            Expression::Unary {
                operator, operand, ..
            } => write!(f, "({} {})", operator, operand),
            Expression::Binary {
                operator,
                left,
                right,
                ..
            } => write!(f, "({} {} {})", operator, left, right),
            Expression::FunctionCall { name, args, .. } => {
                let name = resolve_string_id(*name).expect("invalid function call name");
                write!(f, "{}(", name)?;
                let mut first = true;
                for arg in args.iter() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                    first = false;
                }
                write!(f, ")")
            }
        }
    }
}

// AST allocator

#[derive(Default)]
pub struct AstAllocator {
    arena: bumpalo::Bump,
    next_block_id: Cell<BlockId>,
}

impl AstAllocator {
    pub fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    pub fn next_block_id(&self) -> BlockId {
        let block_id = self.next_block_id.get();
        self.next_block_id.set(block_id.next());
        block_id
    }

    pub fn new_bump_vec<T>(&self) -> BumpVec<'_, T> {
        BumpVec::new_in(&self.arena)
    }

    pub fn new_bump_vec_with_capacity<T>(&self, capacity: usize) -> BumpVec<T> {
        BumpVec::with_capacity_in(capacity, &self.arena)
    }

    pub fn new_bump_vec_from_iter<T>(&self, iter: impl IntoIterator<Item = T>) -> BumpVec<T> {
        BumpVec::from_iter_in(iter, &self.arena)
    }

    pub fn new_bump_vec_from_iter_result<T, E>(
        &self,
        iter: impl IntoIterator<Item = Result<T, E>>,
    ) -> Result<BumpVec<T>, E> {
        let temp_vec = iter.into_iter().collect::<Result<Vec<T>, E>>()?;
        let bump_vec = BumpVec::from_iter_in(temp_vec, &self.arena);
        Ok(bump_vec)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parsed_ast::ParsedAstAllocator;

    #[test]
    fn can_allocate_via_ast() {
        let ast_allocator = ParsedAstAllocator::default();
        let id = ast_allocator.literal_integer(1);
        assert_eq!(
            id,
            &Expression::Literal {
                resolved_type: (),
                value: LiteralValue::Integer(1)
            }
        );
    }

    #[test]
    fn format_expressions() {
        let ast_allocator = ParsedAstAllocator::default();

        let x = ast_allocator.identifier("x");
        let one = ast_allocator.literal_integer(1);
        let sum = ast_allocator.binary(BinaryOperator::Add, x, one);
        let two = ast_allocator.literal_double(2.1);
        let neg = ast_allocator.unary(UnaryOperator::Neg, two);
        let mul = ast_allocator.binary(BinaryOperator::Mul, sum, neg);
        let lt = ast_allocator.binary(BinaryOperator::Lt, mul, ast_allocator.literal_double(4.2));
        let true_lit = ast_allocator.literal_boolean(true);
        let or = ast_allocator.binary(BinaryOperator::Or, lt, true_lit);
        assert_eq!(or.to_string(), "(|| (< (* (+ x 1i) (- 2.1d)) 4.2d) true)");
    }

    #[test]
    fn format_block() {
        let ast_allocator = ParsedAstAllocator::default();

        let block_id = ast_allocator.next_block_id();
        let x = ast_allocator.identifier("x");
        let statement = ast_allocator.statement_expression(x);
        let mut statements = ast_allocator.statements();
        statements.push(statement);
        let block = ast_allocator.block_from_statements(block_id, statements);

        assert_eq!(
            block.to_string(),
            r"{ #0
x;
}"
        );
    }

    #[test]
    fn format_function() {
        let ast_allocator = ParsedAstAllocator::default();

        let block_id = ast_allocator.next_block_id();
        let x = ast_allocator.identifier("x");
        let statements = ast_allocator.statements();
        let block = ast_allocator.block_from_statements(block_id, statements);

        let mut args = ast_allocator.function_arguments();
        args.push(FunctionArgument {
            name: intern_string("x"),
            arg_type: intern_string("int"),
        });
        let fun = ast_allocator.function_declaration("foo", None, args, block);

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
