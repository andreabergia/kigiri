use crate::types::Type;
use kigiri_memory::{BumpVec, StringId, resolve_string_id};
use parser::{
    AstAllocator, Block, CompilationPhase, Expression, FunctionDeclaration, FunctionSignature,
    IfElseBlock, IfStatement, Module, Statement,
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::sync::{LazyLock, Mutex};

#[derive(Debug, PartialEq)]
pub struct PhaseTypeResolved<'a> {
    phantom: PhantomData<&'a ()>,
}

impl<'a> CompilationPhase for PhaseTypeResolved<'a> {
    type SymbolTableType = &'a SymbolTable<'a>;
    type FunctionArgumentType = &'a Symbol<'a>;
    type ExpressionType = Option<Type>;
    type UnaryBinaryOperandType = Type;
    type IdentifierType = SymbolId;
    type FunctionReturnType = Type;
    type FunctionCallReturnType = Option<Type>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VariableIndex {
    index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArgumentIndex {
    index: u32,
}

#[derive(Debug, PartialEq, Clone)]
pub enum SymbolKind<'a> {
    Function {
        signature: &'a FunctionSignature<'a, PhaseTypeResolved<'a>>,
    },
    Variable {
        index: VariableIndex,
        variable_type: Type,
    },
    Argument {
        index: ArgumentIndex,
        argument_type: Type,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct Symbol<'a> {
    pub id: SymbolId,
    pub name: StringId,
    pub kind: SymbolKind<'a>,
    // TODO: declaration location (span)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

#[derive(Debug, PartialEq)]
pub struct SymbolTable<'a> {
    allocated_symbols: RefCell<BumpVec<'a, &'a Symbol<'a>>>,
    symbols_by_id: RefCell<HashMap<SymbolId, &'a Symbol<'a>>>,
    symbols_by_name: RefCell<HashMap<StringId, &'a Symbol<'a>>>,
    parent: Option<&'a SymbolTable<'a>>,
    num_variables: RefCell<usize>,
}

#[derive(Debug, PartialEq)]
pub struct SymbolAndId<'a> {
    pub id: SymbolId,
    pub symbol: &'a Symbol<'a>,
}

#[derive(Debug, Default)]
pub(crate) struct SymbolIdSequencer {
    next_id: u32,
}

// Display

pub struct TypeResolvedModule<'a, 'b, 'c> {
    module: &'a Module<'b, PhaseTypeResolved<'c>>,
}

impl<'a, 'b, 'c> TypeResolvedModule<'a, 'b, 'c> {
    pub fn display(module: &'a Module<'b, PhaseTypeResolved<'c>>) -> String {
        Self { module }.to_string()
    }
}

impl Display for TypeResolvedModule<'_, '_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let module_name = resolve_string_id(self.module.name).ok_or(std::fmt::Error)?;
        writeln!(f, "module {}", module_name)?;
        writeln!(f)?;
        for function in &self.module.functions {
            write_function_declaration(f, function)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

fn write_function_declaration(
    f: &mut Formatter<'_>,
    function_declaration: &FunctionDeclaration<PhaseTypeResolved>,
) -> std::fmt::Result {
    let function_name =
        resolve_string_id(function_declaration.signature.name).ok_or(std::fmt::Error)?;
    writeln!(f, "fn {}(", function_name)?;
    for arg in function_declaration.signature.arguments.iter() {
        let symbol_name = resolve_string_id(arg.name).ok_or(std::fmt::Error)?;
        writeln!(f, "  {}: {},", symbol_name, Type::name(arg.symbol_type()))?;
    }
    writeln!(
        f,
        ") -> {}",
        match &function_declaration.signature.return_type {
            Some(return_type) => return_type.to_string(),
            None => "void".to_string(),
        }
    )?;
    fmt_block(
        f,
        function_declaration.body,
        DisplayTypedAstContext {
            indent: "".to_owned(),
            symbol_table: function_declaration.body.symbol_table,
        },
    )
}

pub struct TypeResolvedBlock<'a, 'b, 'c> {
    block: &'a Block<'b, PhaseTypeResolved<'c>>,
}

impl<'a, 'b, 'c> TypeResolvedBlock<'a, 'b, 'c> {
    pub fn display(block: &'a Block<'b, PhaseTypeResolved<'c>>) -> String {
        Self { block }.to_string()
    }
}

impl Display for TypeResolvedBlock<'_, '_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_block(
            f,
            self.block,
            DisplayTypedAstContext {
                indent: "".to_owned(),
                symbol_table: self.block.symbol_table,
            },
        )
    }
}

#[derive(Debug, Clone)]
struct DisplayTypedAstContext<'a> {
    indent: String,
    symbol_table: &'a SymbolTable<'a>,
}

impl DisplayTypedAstContext<'_> {
    fn indented(&self) -> Self {
        Self {
            indent: format!("{}  ", self.indent),
            symbol_table: self.symbol_table,
        }
    }
}

fn fmt_block(
    f: &mut Formatter<'_>,
    block: &Block<PhaseTypeResolved>,
    context: DisplayTypedAstContext,
) -> std::fmt::Result {
    writeln!(f, "{{ #{}", block.id.0)?;
    let block_context = DisplayTypedAstContext {
        indent: context.indent.clone(),
        symbol_table: block.symbol_table,
    };
    for statement in &block.statements {
        fmt_statement(f, statement, &block_context)?;
    }
    writeln!(f, "{}}}", context.indent)
}

impl Symbol<'_> {
    fn name(&self) -> Result<&str, std::fmt::Error> {
        resolve_string_id(self.name).ok_or(std::fmt::Error)
    }

    pub fn symbol_type(&self) -> Option<Type> {
        match self.kind {
            // TODO: this should be a more complex type that can be "int" or "(int) -> double"
            SymbolKind::Function { .. } => None,
            SymbolKind::Variable { variable_type, .. } => Some(variable_type),
            SymbolKind::Argument { argument_type, .. } => Some(argument_type),
        }
    }
}

impl Display for Symbol<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name()?, Type::name(self.symbol_type()))
    }
}

impl Display for ArgumentIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.index)
    }
}

impl Display for VariableIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.index)
    }
}

fn fmt_statement(
    f: &mut Formatter<'_>,
    statement: &Statement<PhaseTypeResolved>,
    context: &DisplayTypedAstContext,
) -> std::fmt::Result {
    match statement {
        Statement::Let { initializers } => {
            write!(f, "{}  let ", context.indent)?;
            let mut first = true;
            for initializer in initializers.iter() {
                if !first {
                    write!(f, ", ")?;
                }
                let symbol = context
                    .symbol_table
                    .lookup_by_id(initializer.variable)
                    .ok_or(std::fmt::Error)?;
                write!(f, "{} = ", symbol)?;
                fmt_expression(f, initializer.value, context.symbol_table)?;
                first = false;
            }
            writeln!(f, ";")
        }
        Statement::Assignment { target, expression } => {
            let symbol = context.symbol_table.lookup_by_id(*target);
            if let Some(symbol) = symbol {
                write!(f, "{}  {} = ", context.indent, symbol.name()?)?;
                fmt_expression(f, expression, context.symbol_table)?;
                writeln!(f, ";")
            } else {
                Err(std::fmt::Error)
            }
        }
        Statement::Return { expression } => {
            if let Some(value) = expression {
                write!(f, "{}  return ", context.indent)?;
                fmt_expression(f, value, context.symbol_table)?;
            } else {
                write!(f, "{}  return", context.indent,)?;
            }
            writeln!(f, ";")
        }
        Statement::Expression { expression } => {
            write!(f, "{}  ", context.indent)?;
            fmt_expression(f, expression, context.symbol_table)?;
            writeln!(f, ";")
        }
        Statement::NestedBlock { block } => {
            write!(f, "{}  ", context.indent)?;
            fmt_block(f, block, context.indented())
        }
        Statement::If(if_statement) => {
            fmt_if_statement(f, if_statement, context, &format!("{}  ", context.indent))
        }
        Statement::While(while_statement) => {
            write!(f, "{}  while ", context.indent)?;
            fmt_expression(f, while_statement.condition, context.symbol_table)?;
            write!(f, " ")?;
            fmt_block(f, while_statement.body, context.indented())
        }
        Statement::Break => {
            write!(f, "{}  break", context.indent)
        }
        Statement::Continue => {
            write!(f, "{}  continue", context.indent)
        }
    }
}

fn fmt_if_statement(
    f: &mut Formatter<'_>,
    if_statement: &IfStatement<PhaseTypeResolved>,
    context: &DisplayTypedAstContext,
    if_prefix: &str,
) -> std::fmt::Result {
    write!(f, "{}if ", if_prefix)?;
    fmt_expression(f, if_statement.condition, context.symbol_table)?;
    write!(f, " ")?;
    fmt_block(f, if_statement.then_block, context.indented())?;
    if let Some(else_block) = if_statement.else_block {
        write!(f, "{}  else ", context.indent)?;
        fmt_if_else_block(f, else_block, context)?;
    }
    Ok(())
}

fn fmt_if_else_block(
    f: &mut Formatter<'_>,
    else_block: &IfElseBlock<PhaseTypeResolved>,
    context: &DisplayTypedAstContext,
) -> std::fmt::Result {
    match else_block {
        IfElseBlock::Block(block) => fmt_block(f, block, context.indented()),
        IfElseBlock::If(if_statement) => {
            // For else if, we don't want extra indentation since it's part of the same if chain
            fmt_if_statement(f, if_statement, context, "  ")
        }
    }
}

struct TypedExpressionSymbolTableDisplayHelper<'e, 's, 't, 'p> {
    expression: &'e Expression<'e, PhaseTypeResolved<'p>>,
    symbol_table: &'s SymbolTable<'t>,
}

impl Display for TypedExpressionSymbolTableDisplayHelper<'_, '_, '_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_expression(f, self.expression, self.symbol_table)
    }
}

pub fn to_string_with_symbol_table(
    expression: &Expression<PhaseTypeResolved>,
    symbol_table: &SymbolTable<'_>,
) -> String {
    TypedExpressionSymbolTableDisplayHelper {
        expression,
        symbol_table,
    }
    .to_string()
}

fn fmt_expression(
    f: &mut Formatter<'_>,
    expression: &Expression<PhaseTypeResolved>,
    symbol_table: &SymbolTable<'_>,
) -> std::fmt::Result {
    match expression {
        Expression::Identifier {
            name: symbol_id, ..
        } => match symbol_table.lookup_by_id(*symbol_id) {
            None => Err(std::fmt::Error),
            Some(symbol) => {
                write!(f, "{}", symbol.name()?)
            }
        },
        Expression::Literal { value, .. } => {
            write!(f, "{}", value)
        }
        Expression::Unary {
            resolved_type,
            operator,
            operand,
        } => {
            write!(f, "({}{} ", operator, resolved_type.to_string_short(),)?;
            fmt_expression(f, operand, symbol_table)?;
            write!(f, ")")
        }
        Expression::Binary {
            result_type,
            operator,
            left,
            right,
            ..
        } => {
            write!(f, "({}{} ", operator, result_type.to_string_short(),)?;
            fmt_expression(f, left, symbol_table)?;
            write!(f, " ")?;
            fmt_expression(f, right, symbol_table)?;
            write!(f, ")")
        }
        Expression::FunctionCall { name, args, .. } => {
            let symbol = symbol_table.lookup_by_id(*name).ok_or(std::fmt::Error)?;
            write!(f, "{}(", symbol.name()?)?;
            let mut first = true;
            for arg in args.iter() {
                if !first {
                    write!(f, ", ")?;
                }
                fmt_expression(f, arg, symbol_table)?;
                first = false;
            }
            write!(f, ")")
        }
    }
}

// Impls

impl SymbolIdSequencer {
    pub fn next(&mut self) -> SymbolId {
        let id = SymbolId(self.next_id);
        self.next_id += 1;
        id
    }
}

static SYMBOL_ID_SEQUENCER: LazyLock<Mutex<SymbolIdSequencer>> =
    LazyLock::new(|| Mutex::new(SymbolIdSequencer::default()));

fn next_symbol_id() -> Result<SymbolId, crate::semantic_analyzer::SemanticAnalysisError> {
    Ok(SYMBOL_ID_SEQUENCER
        .lock()
        .map_err(
            |_| crate::semantic_analyzer::SemanticAnalysisError::InternalError {
                message: "failed to acquire lock for symbol ID sequencer".to_string(),
            },
        )?
        .next())
}

impl From<VariableIndex> for usize {
    fn from(val: VariableIndex) -> Self {
        val.index
    }
}

impl From<usize> for VariableIndex {
    fn from(val: usize) -> Self {
        VariableIndex { index: val }
    }
}

impl From<ArgumentIndex> for u32 {
    fn from(val: ArgumentIndex) -> Self {
        val.index
    }
}

impl From<u32> for ArgumentIndex {
    fn from(val: u32) -> Self {
        ArgumentIndex { index: val }
    }
}

impl<'a> SymbolTable<'a> {
    pub fn new(allocator: &'a AstAllocator, parent: Option<&'a SymbolTable<'a>>) -> &'a Self {
        allocator.alloc(Self {
            allocated_symbols: RefCell::new(allocator.new_bump_vec()),
            symbols_by_id: RefCell::new(HashMap::new()),
            symbols_by_name: RefCell::new(HashMap::new()),
            parent,
            num_variables: RefCell::new(0),
        })
    }

    pub fn new_global(allocator: &'a AstAllocator, capacity: usize) -> &'a Self {
        allocator.alloc(Self {
            allocated_symbols: RefCell::new(allocator.new_bump_vec_with_capacity(capacity)),
            symbols_by_id: RefCell::new(HashMap::with_capacity(capacity)),
            symbols_by_name: RefCell::new(HashMap::with_capacity(capacity)),
            parent: None,
            num_variables: RefCell::new(0),
        })
    }

    fn root(&'a self) -> &'a SymbolTable<'a> {
        if let Some(parent) = self.parent {
            parent.root()
        } else {
            self
        }
    }

    pub fn add_symbol(
        &'a self,
        allocator: &'a AstAllocator,
        name: StringId,
        kind: SymbolKind<'a>,
    ) -> Result<SymbolAndId<'a>, crate::semantic_analyzer::SemanticAnalysisError> {
        if let SymbolKind::Variable { .. } = kind {
            let root = self.root();
            *root.num_variables.borrow_mut() += 1;
        }

        let id = next_symbol_id()?;
        let symbol = allocator.alloc(Symbol { id, name, kind });

        // This allows for name shadowing!
        self.allocated_symbols.borrow_mut().push(symbol);
        self.symbols_by_name.borrow_mut().insert(name, symbol);
        self.symbols_by_id.borrow_mut().insert(id, symbol);

        Ok(SymbolAndId { id, symbol })
    }

    pub fn lookup_by_name(&self, name: StringId) -> Option<&'a Symbol<'a>> {
        self.symbols_by_name
            .borrow()
            .get(&name)
            .cloned()
            .or_else(|| self.parent.and_then(|parent| parent.lookup_by_name(name)))
    }

    pub fn lookup_by_id(&self, id: SymbolId) -> Option<&'a Symbol<'a>> {
        self.symbols_by_id
            .borrow()
            .get(&id)
            .cloned()
            .or_else(|| self.parent.and_then(|parent| parent.lookup_by_id(id)))
    }

    pub fn len(&self) -> usize {
        self.allocated_symbols.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.allocated_symbols.borrow().is_empty()
    }

    pub fn next_variable_index(&'a self) -> VariableIndex {
        // Variable indices should be global across the function, so delegate to root
        let root = self.root();
        VariableIndex::from(*root.num_variables.borrow())
    }
}

pub fn resolved_type(expression: &Expression<'_, PhaseTypeResolved<'_>>) -> Option<Type> {
    match expression {
        Expression::Identifier { resolved_type, .. } => *resolved_type,
        Expression::Literal { resolved_type, .. } => *resolved_type,
        Expression::Unary { resolved_type, .. } => Some(*resolved_type),
        Expression::Binary { result_type, .. } => Some(*result_type),
        Expression::FunctionCall { return_type, .. } => *return_type,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::{BinaryOperator, BlockId, LiteralValue};

    #[test]
    fn display_contains_type_after_operator() {
        let typed_expression: Expression<PhaseTypeResolved> = Expression::Binary {
            result_type: Type::Int,
            operator: BinaryOperator::Add,
            operand_type: Type::Int,
            left: &Expression::Literal {
                resolved_type: Some(Type::Int),
                value: LiteralValue::Integer(1),
            },
            right: &Expression::Literal {
                resolved_type: Some(Type::Int),
                value: LiteralValue::Integer(2),
            },
        };

        let allocator = AstAllocator::default();
        let symbol_table = SymbolTable::new(&allocator, None);

        assert_eq!(
            to_string_with_symbol_table(&typed_expression, symbol_table),
            "(+i 1i 2i)"
        );
    }

    #[test]
    fn display_block() {
        let allocator = AstAllocator::default();
        let block: &Block<PhaseTypeResolved> = make_block_with_return_1i(&allocator);
        assert_eq!(
            TypeResolvedBlock::display(block),
            r"{ #1
  return 1i;
}
"
        );
    }

    fn make_block_with_return_1i(allocator: &AstAllocator) -> &Block<PhaseTypeResolved> {
        let symbol_table: &SymbolTable = SymbolTable::new(allocator, None);
        let block = allocator.alloc(Block {
            id: BlockId(1),
            statements: allocator.new_bump_vec_from_iter(vec![allocator.alloc(
                Statement::Return {
                    expression: Some(allocator.alloc(Expression::Literal {
                        resolved_type: Some(Type::Int),
                        value: LiteralValue::Integer(1),
                    })),
                },
            )]),
            symbol_table,
        });
        block
    }

    #[test]
    fn display_block_nested() {
        let allocator = AstAllocator::default();

        let outer_symbol_table = allocator.alloc(SymbolTable::new(&allocator, None));
        let mut outer: Block<PhaseTypeResolved> = Block {
            id: BlockId(2),
            statements: allocator.new_bump_vec(),
            symbol_table: outer_symbol_table,
        };

        let inner = make_block_with_return_1i(&allocator);
        outer
            .statements
            .push(allocator.alloc(Statement::NestedBlock { block: inner }));

        assert_eq!(
            TypeResolvedBlock::display(&outer),
            r"{ #2
  { #1
    return 1i;
  }
}
"
        );
    }
}
