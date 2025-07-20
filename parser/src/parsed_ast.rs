use crate::symbols::StringId;
use crate::{
    AstAllocator, BinaryOperator, Block, BlockId, CompilationPhase, Expression, FunctionArgument,
    FunctionDeclaration, FunctionSignature, IfElseBlock, IfStatement, LetInitializer, LiteralValue,
    Module, Statement, UnaryOperator, intern_string,
};
use bumpalo::collections::Vec as BumpVec;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::marker::PhantomData;

#[derive(Debug, PartialEq)]
pub struct PhaseParsed<'a> {
    phantom: PhantomData<&'a ()>,
}

pub type FunctionSignaturesByName<'a, Phase> = HashMap<StringId, &'a FunctionSignature<'a, Phase>>;

impl CompilationPhase for PhaseParsed<'_> {
    type SymbolTableType = ();
    type FunctionArgumentType = FunctionArgument;
    type ExpressionType = ();
    type UnaryBinaryOperandType = ();
    type IdentifierType = StringId;
    type FunctionReturnType = StringId;
    type FunctionCallReturnType = ();
}

#[derive(Default)]
pub struct ParsedAstAllocator {
    allocator: AstAllocator,
}

impl ParsedAstAllocator {
    pub fn identifier(&self, symbol: &str) -> &Expression<PhaseParsed> {
        self.allocator.alloc(Expression::Identifier {
            resolved_type: (),
            name: intern_string(symbol),
        })
    }

    pub fn literal_int(&self, value: i64) -> &Expression<PhaseParsed> {
        self.allocator.alloc(Expression::Literal {
            resolved_type: (),
            value: LiteralValue::Integer(value),
        })
    }

    pub fn literal_double(&self, value: f64) -> &Expression<PhaseParsed> {
        self.allocator.alloc(Expression::Literal {
            resolved_type: (),
            value: LiteralValue::Double(value),
        })
    }

    pub fn literal_bool(&self, value: bool) -> &Expression<PhaseParsed> {
        self.allocator.alloc(Expression::Literal {
            resolved_type: (),
            value: LiteralValue::Boolean(value),
        })
    }

    pub fn unary<'s, 'l>(
        &'s self,
        operator: UnaryOperator,
        operand: &'l Expression<'l, PhaseParsed<'s>>,
    ) -> &'s Expression<'s, PhaseParsed<'s>>
    where
        'l: 's,
    {
        self.allocator.alloc(Expression::Unary {
            resolved_type: (),
            operator,
            operand,
        })
    }

    pub fn binary<'s, 'l, 'r>(
        &'s self,
        operator: BinaryOperator,
        left: &'l Expression<PhaseParsed<'s>>,
        right: &'r Expression<PhaseParsed<'s>>,
    ) -> &'s Expression<'s, PhaseParsed<'s>>
    where
        'l: 's,
        'r: 's,
    {
        self.allocator.alloc(Expression::Binary {
            result_type: (),
            operator,
            operand_type: (),
            left,
            right,
        })
    }

    pub fn function_call_arguments(&self) -> BumpVec<&Expression<PhaseParsed>> {
        self.allocator.new_bump_vec()
    }

    pub fn function_call<'s, 'e>(
        &'s self,
        name: &str,
        args: BumpVec<'e, &'e Expression<'e, PhaseParsed<'s>>>,
    ) -> &'s Expression<'s, PhaseParsed<'s>>
    where
        'e: 's,
    {
        self.allocator.alloc(Expression::FunctionCall {
            name: intern_string(name),
            args,
            return_type: (),
        })
    }

    pub fn statements(&self) -> BumpVec<&Statement<PhaseParsed>> {
        self.allocator.new_bump_vec()
    }

    pub fn next_block_id(&self) -> BlockId {
        self.allocator.next_block_id()
    }

    pub fn block_from_statements<'s, 'v>(
        &'s self,
        block_id: BlockId,
        statements: BumpVec<'v, &'v Statement<PhaseParsed<'s>>>,
    ) -> &'s Block<'s, PhaseParsed<'s>>
    where
        'v: 's,
    {
        self.allocator.alloc(Block {
            id: block_id,
            statements,
            symbol_table: (),
        })
    }

    pub fn nested_block<'s, 'b>(
        &'s self,
        block: &'b Block<'b, PhaseParsed<'s>>,
    ) -> &'s Statement<'s, PhaseParsed<'s>>
    where
        'b: 's,
    {
        self.allocator.alloc(Statement::NestedBlock { block })
    }

    pub fn statement_expression<'s, 'e>(
        &'s self,
        expression: &'e Expression<'e, PhaseParsed<'s>>,
    ) -> &'s Statement<'s, PhaseParsed<'s>>
    where
        'e: 's,
    {
        self.allocator.alloc(Statement::Expression { expression })
    }

    pub fn statement_return<'s, 'e>(
        &'s self,
        expression: Option<&'e Expression<'e, PhaseParsed<'s>>>,
    ) -> &'s Statement<'s, PhaseParsed<'s>>
    where
        'e: 's,
    {
        self.allocator.alloc(Statement::Return { expression })
    }

    pub fn statement_let_initializers(&self) -> BumpVec<LetInitializer<PhaseParsed>> {
        self.allocator.new_bump_vec()
    }

    pub fn statement_let<'s, 'e>(
        &'s self,
        initializers: BumpVec<'e, LetInitializer<'e, PhaseParsed<'s>>>,
    ) -> &'s Statement<'s, PhaseParsed<'s>>
    where
        'e: 's,
    {
        self.allocator.alloc(Statement::Let { initializers })
    }

    pub fn statement_assignment<'s, 'e>(
        &'s self,
        name: &str,
        expression: &'e Expression<'e, PhaseParsed<'s>>,
    ) -> &'s Statement<'s, PhaseParsed<'s>>
    where
        'e: 's,
    {
        self.allocator.alloc(Statement::Assignment {
            target: intern_string(name),
            expression,
        })
    }

    pub fn functions(&self) -> BumpVec<&FunctionDeclaration<PhaseParsed>> {
        self.allocator.new_bump_vec()
    }

    pub fn module<'s, 'f, 'f2>(
        &'s self,
        module_name: &str,
        functions: BumpVec<'f, &'f2 FunctionDeclaration<'f, PhaseParsed<'s>>>,
        function_signatures: FunctionSignaturesByName<'f2, PhaseParsed<'f2>>,
    ) -> &'s Module<'s, PhaseParsed<'s>>
    where
        'f: 's,
        'f2: 's,
    {
        let name = intern_string(module_name);
        self.allocator.alloc(Module {
            name,
            functions,
            function_signatures,
        })
    }

    pub fn function_arguments(&self) -> BumpVec<FunctionArgument> {
        self.allocator.new_bump_vec()
    }

    pub fn function_declaration<'s, 'a, 'b>(
        &'s self,
        name: &str,
        return_type: Option<StringId>,
        arguments: BumpVec<'a, FunctionArgument>,
        body: &'b Block<'b, PhaseParsed<'s>>,
    ) -> &'s FunctionDeclaration<'s, PhaseParsed<'s>>
    where
        'a: 's,
        'b: 's,
    {
        self.allocator.alloc(FunctionDeclaration {
            signature: self.allocator.alloc(FunctionSignature {
                name: intern_string(name),
                return_type,
                arguments,
            }),
            body,
            symbol_table: (),
        })
    }

    pub fn statement_if<'s, 'c, 'b, 'e>(
        &'s self,
        condition: &'c Expression<'c, PhaseParsed<'s>>,
        then_block: &'b Block<'b, PhaseParsed<'s>>,
        else_block: Option<&'e IfElseBlock<'e, PhaseParsed<'s>>>,
    ) -> &'s Statement<'s, PhaseParsed<'s>>
    where
        'c: 's,
        'b: 's,
        'e: 's,
    {
        self.allocator.alloc(Statement::If {
            condition,
            then_block,
            else_block,
        })
    }

    pub fn if_else_block<'s, 'b>(
        &'s self,
        block: &'b Block<'b, PhaseParsed<'s>>,
    ) -> &'s IfElseBlock<'s, PhaseParsed<'s>>
    where
        'b: 's,
    {
        self.allocator.alloc(IfElseBlock::Block(block))
    }

    pub fn if_else_if<'s, 'c, 't, 'e>(
        &'s self,
        condition: &'c Expression<'c, PhaseParsed<'s>>,
        then_block: &'t Block<'t, PhaseParsed<'s>>,
        else_block: Option<&'e IfElseBlock<'e, PhaseParsed<'s>>>,
    ) -> &'s IfElseBlock<'s, PhaseParsed<'s>>
    where
        'c: 's,
        't: 's,
        'e: 's,
    {
        let if_statement = self.allocator.alloc(IfStatement {
            condition,
            then_block,
            else_block,
        });
        self.allocator.alloc(IfElseBlock::If(if_statement))
    }
}
