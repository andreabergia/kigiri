use crate::types::Type;
use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use parser::{BinaryOperator, BlockId, LiteralValue, StringId, UnaryOperator, resolve_string_id};
use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::sync::{LazyLock, Mutex};

pub type TypedFunctionSignaturesByName<'a> = HashMap<StringId, &'a TypedFunctionSignature<'a>>;

#[derive(Debug, PartialEq)]
pub struct TypedModule<'a> {
    pub name: StringId,
    pub functions: BumpVec<'a, &'a TypedFunctionDeclaration<'a>>,
    pub function_signatures: TypedFunctionSignaturesByName<'a>,
}

#[derive(Debug, PartialEq)]
pub struct TypedFunctionDeclaration<'a> {
    pub signature: &'a TypedFunctionSignature<'a>,
    pub body: &'a TypedBlock<'a>,
}

#[derive(Debug, PartialEq)]
pub struct TypedFunctionSignature<'a> {
    pub name: StringId,
    pub return_type: Option<Type>,
    pub arguments: BumpVec<'a, SymbolId>,
}

#[derive(Debug, PartialEq)]
pub enum TypedStatement<'a> {
    // Let gets flattened, i.e. one statement in the AST with multiple variables
    // will be represented as multiple Let typed statements.
    Let {
        symbol: SymbolId,
        value: &'a TypedExpression<'a>,
    },
    Assignment {
        symbol: SymbolId,
        value: &'a TypedExpression<'a>,
    },
    Return {
        value: Option<&'a TypedExpression<'a>>,
    },
    Expression {
        expression: &'a TypedExpression<'a>,
    },
    NestedBlock {
        block: &'a TypedBlock<'a>,
    },
}

#[derive(Debug, PartialEq)]
pub struct TypedBlock<'a> {
    pub id: BlockId,
    pub statements: BumpVec<'a, &'a TypedStatement<'a>>,
    pub symbol_table: &'a SymbolTable<'a>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: StringId,
    pub symbol_type: Type,
    // TODO: declaration location (span)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

#[derive(Debug, PartialEq)]
pub struct SymbolTable<'a> {
    allocated_symbols: RefCell<BumpVec<'a, &'a Symbol>>,
    symbols_by_id: RefCell<HashMap<SymbolId, &'a Symbol>>,
    symbols_by_name: RefCell<HashMap<StringId, &'a Symbol>>,
    parent: Option<&'a SymbolTable<'a>>,
}

#[derive(Debug, Default)]
pub(crate) struct SymbolIdSequencer {
    next_id: u32,
}

#[derive(Debug, PartialEq)]
pub enum TypedExpression<'a> {
    // Identifier {
    //     resolved_type: Type,
    //     symbol_id: SymbolId,
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

// Display

impl Display for TypedBlock<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_context(
            f,
            DisplayTypedAstContext {
                indent: "".to_owned(),
                symbol_table: self.symbol_table,
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

impl TypedBlock<'_> {
    fn fmt_with_context(
        &self,
        f: &mut Formatter<'_>,
        mut context: DisplayTypedAstContext,
    ) -> std::fmt::Result {
        writeln!(f, "{}{{ #{}", context.indent, self.id.0)?;
        for statement in &self.statements {
            statement.fmt_with_context(f, &context)?;
        }
        writeln!(f, "{}}}", context.indent)
    }
}

impl Symbol {
    fn name(&self) -> &str {
        resolve_string_id(self.name).expect("symbol name")
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name(), self.symbol_type)
    }
}

impl TypedStatement<'_> {
    fn fmt_with_context(
        &self,
        f: &mut Formatter<'_>,
        mut context: &DisplayTypedAstContext,
    ) -> std::fmt::Result {
        match self {
            TypedStatement::Let { symbol, value } => {
                let symbol = context.symbol_table.lookup_by_id(*symbol);
                if let Some(symbol) = symbol {
                    writeln!(f, "{}  let {} = {};", context.indent, symbol, value)
                } else {
                    Err(std::fmt::Error)
                }
            }
            TypedStatement::Assignment { symbol, value } => {
                let symbol = context.symbol_table.lookup_by_id(*symbol);
                if let Some(symbol) = symbol {
                    writeln!(f, "{}  {} = {};", context.indent, symbol.name(), value)
                } else {
                    Err(std::fmt::Error)
                }
            }
            TypedStatement::Return { value } => {
                if let Some(value) = value {
                    writeln!(f, "{}  return {};", context.indent, value)
                } else {
                    writeln!(f, "{}  return;", context.indent,)
                }
            }
            TypedStatement::Expression { expression } => {
                writeln!(f, "{}  {};", context.indent, expression)
            }
            TypedStatement::NestedBlock { block } => block.fmt_with_context(f, context.indented()),
        }
    }
}

impl Display for TypedExpression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            // Expression::Identifier {
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

fn next_symbol_id() -> SymbolId {
    SYMBOL_ID_SEQUENCER
        .lock()
        .expect("should be able to lock the sequencer")
        .next()
}

impl<'a> SymbolTable<'a> {
    pub fn new(arena: &'a Bump, parent: Option<&'a SymbolTable<'a>>) -> Self {
        Self {
            allocated_symbols: RefCell::new(BumpVec::new_in(arena)),
            symbols_by_id: RefCell::new(HashMap::new()),
            symbols_by_name: RefCell::new(HashMap::new()),
            parent,
        }
    }

    pub fn add_symbol(&self, allocator: &'a Bump, name: StringId, symbol_type: Type) -> SymbolId {
        let id = next_symbol_id();
        let symbol = allocator.alloc(Symbol {
            id,
            name,
            symbol_type,
        });

        // This allows for name shadowing!
        self.allocated_symbols.borrow_mut().push(symbol);
        self.symbols_by_name.borrow_mut().insert(name, symbol);
        self.symbols_by_id.borrow_mut().insert(id, symbol);

        id
    }

    pub fn lookup_by_name(&self, name: StringId) -> Option<&Symbol> {
        self.symbols_by_name
            .borrow()
            .get(&name)
            .cloned()
            .or_else(|| self.parent.and_then(|parent| parent.lookup_by_name(name)))
    }

    pub fn lookup_by_id(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols_by_id
            .borrow()
            .get(&id)
            .cloned()
            .or_else(|| self.parent.and_then(|parent| parent.lookup_by_id(id)))
    }

    pub fn len(&self) -> usize {
        self.allocated_symbols.borrow().len()
    }
}

impl TypedExpression<'_> {
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
    use bumpalo::Bump;

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

    #[test]
    fn display_block() {
        let arena = Bump::new();
        let block = make_block_with_return_1i(&arena);
        assert_eq!(
            block.to_string(),
            r"{ #1
  return 1i;
}
"
        );
    }

    fn make_block_with_return_1i(arena: &Bump) -> &TypedBlock {
        let mut block = arena.alloc(TypedBlock {
            id: BlockId(1),
            statements: BumpVec::new_in(arena),
            symbol_table: arena.alloc(SymbolTable::new(arena, None)),
        });
        block.statements.push(arena.alloc(TypedStatement::Return {
            value: Some(arena.alloc(TypedExpression::Literal {
                resolved_type: Type::Int,
                value: LiteralValue::Integer(1),
            })),
        }));
        block
    }

    #[test]
    fn display_block_nested() {
        let arena = Bump::new();

        let outer_symbol_table = arena.alloc(SymbolTable::new(&arena, None));
        let mut outer = TypedBlock {
            id: BlockId(2),
            statements: BumpVec::new_in(&arena),
            symbol_table: outer_symbol_table,
        };

        let mut inner = make_block_with_return_1i(&arena);
        outer
            .statements
            .push(arena.alloc(TypedStatement::NestedBlock { block: inner }));

        assert_eq!(
            outer.to_string(),
            r"{ #2
  { #1
    return 1i;
  }
}
"
        );
    }
}
