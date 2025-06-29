use crate::typed_ast::{
    SymbolId, SymbolTable, TypedBlock, TypedFunctionDeclaration, TypedFunctionSignature,
    TypedFunctionSignaturesByName, TypedModule, TypedStatement,
};
use crate::{ArgumentIndex, SymbolKind, Type, TypedExpression, VariableIndex};
use bumpalo::collections::Vec as BumpVec;
use parser::{
    BinaryOperator, Expression, Module, Statement, StringId, UnaryOperator, resolve_string_id,
};
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
    #[error("symbol not found: \"{name}\"")]
    SymbolNotFound { name: String },
    #[error(
        "invalid assignment to \"{symbol_name}\": symbol has type {symbol_type}, but expression has type {expression_type}"
    )]
    MismatchedAssignmentType {
        symbol_name: String,
        symbol_type: Type,
        expression_type: Type,
    },
    #[error("cannot assign value to function \"{name}\"")]
    CannotAssignToFunction { name: String },
    #[error("type not found: \"{type_name}\"")]
    TypeNotFound { type_name: String },
}

#[derive(Default)]
pub struct SemanticAnalyzer {
    arena: bumpalo::Bump,
}

impl SemanticAnalyzer {
    pub fn analyze_module<'a>(
        &'a self,
        module: &Module,
    ) -> Result<&'a TypedModule<'a>, SemanticAnalysisError> {
        let mut function_signatures =
            TypedFunctionSignaturesByName::with_capacity(module.function_signatures.len());
        let mut functions = BumpVec::with_capacity_in(module.functions.len(), &self.arena);

        for function in module.functions.iter() {
            let function = self.analyze_function(function)?;
            functions.push(function);
            function_signatures.insert(function.signature.name, function.signature);
        }

        Ok(self.alloc({
            TypedModule {
                name: module.name,
                functions,
                function_signatures,
            }
        }))
    }

    fn analyze_function<'a>(
        &'a self,
        function: &parser::FunctionDeclaration,
    ) -> Result<&'a TypedFunctionDeclaration<'a>, SemanticAnalysisError> {
        let symbol_table = self.symbol_table(None);

        let return_type = function
            .signature
            .return_type
            .map(|t| self.parse_type(t))
            .transpose()?;

        let arguments = function
            .signature
            .arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                let arg_type = self.parse_type(argument.arg_type);
                arg_type.map(|arg_type| {
                    symbol_table.add_symbol(
                        &self.arena,
                        argument.name,
                        arg_type,
                        SymbolKind::Argument {
                            index: ArgumentIndex::from(index as u32),
                        },
                    )
                })
            })
            .collect::<Result<Vec<SymbolId>, SemanticAnalysisError>>()?;
        let arguments = BumpVec::from_iter_in(arguments.iter().cloned(), &self.arena);

        let signature = self.alloc(TypedFunctionSignature {
            name: function.signature.name,
            return_type,
            arguments,
        });

        let body = self.analyze_block(function.body, symbol_table)?;

        Ok(self.alloc(TypedFunctionDeclaration {
            signature,
            body,
            symbol_table,
        }))
    }

    fn parse_type(&self, type_name: StringId) -> Result<Type, SemanticAnalysisError> {
        let type_name = resolve_string_id(type_name).expect("should be able to resolve type name");
        match type_name {
            "int" => Ok(Type::Int),
            "double" => Ok(Type::Double),
            "boolean" => Ok(Type::Boolean),
            _ => Err(SemanticAnalysisError::TypeNotFound {
                type_name: type_name.to_string(),
            }),
        }
    }

    fn analyze_block<'a>(
        &'a self,
        block: &parser::Block,
        parent_symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a TypedBlock<'a>, SemanticAnalysisError> {
        let mut statements = BumpVec::with_capacity_in(block.statements.len(), &self.arena);
        for statement in &block.statements {
            self.analyze_statement(statement, &mut statements, parent_symbol_table)?;
        }
        Ok(self.alloc(TypedBlock {
            id: block.id,
            statements,
            symbol_table: parent_symbol_table,
        }))
    }

    fn analyze_statement<'a>(
        &'a self,
        statement: &Statement,
        statements: &mut BumpVec<'a, &'a TypedStatement<'a>>,
        symbol_table: &'a SymbolTable<'a>,
    ) -> Result<(), SemanticAnalysisError> {
        match statement {
            Statement::Let { initializers } => {
                for initializer in initializers {
                    let value = self.analyze_expression(initializer.value, symbol_table)?;

                    let symbol = symbol_table.add_symbol(
                        &self.arena,
                        initializer.name,
                        value.resolved_type(),
                        SymbolKind::Variable {
                            index: next_variable_index(symbol_table),
                        },
                    );
                    statements.push(self.alloc(TypedStatement::Let { symbol, value }));
                }
            }
            Statement::Assignment { name, expression } => {
                let symbol_name = resolve_string_id(*name)
                    .expect("should be able to find string")
                    .to_owned();

                let symbol = symbol_table.lookup_by_name(*name);

                match symbol {
                    None => {
                        return Err(SemanticAnalysisError::SymbolNotFound { name: symbol_name });
                    }
                    Some(symbol) => {
                        let value = self.analyze_expression(expression, symbol_table)?;
                        if value.resolved_type() != symbol.symbol_type {
                            return Err(SemanticAnalysisError::MismatchedAssignmentType {
                                symbol_name,
                                symbol_type: symbol.symbol_type,
                                expression_type: value.resolved_type(),
                            });
                        }

                        match symbol.kind {
                            SymbolKind::Function => {
                                return Err(SemanticAnalysisError::CannotAssignToFunction {
                                    name: symbol_name,
                                });
                            }
                            SymbolKind::Variable { .. } => {
                                statements.push(self.alloc(TypedStatement::Assignment {
                                    symbol: symbol.id,
                                    value,
                                }))
                            }
                            SymbolKind::Argument { index } => {
                                // We actually need to create a new variable and assign to that
                                // one, because LLVM (and thus our IR) does not allow reassigning
                                // a function argument.
                                let new_variable = symbol_table.add_symbol(
                                    &self.arena,
                                    *name,
                                    value.resolved_type(),
                                    SymbolKind::Variable {
                                        index: next_variable_index(symbol_table),
                                    },
                                );
                                statements.push(self.alloc(TypedStatement::Let {
                                    symbol: new_variable,
                                    value,
                                }));
                            }
                        }
                    }
                }
            }
            Statement::Return { expression } => {
                let value = expression
                    .map(|expr| self.analyze_expression(expr, symbol_table))
                    .transpose()?;
                statements.push(self.alloc(TypedStatement::Return { value }));
            }
            Statement::Expression { expression } => {
                let typed_expression = self.analyze_expression(expression, symbol_table)?;
                statements.push(self.alloc(TypedStatement::Expression {
                    expression: typed_expression,
                }))
            }
            Statement::NestedBlock { block } => {
                let nested_symbol_table = self.symbol_table(Some(symbol_table));
                let typed_block = self.analyze_block(block, nested_symbol_table)?;
                statements.push(self.alloc(TypedStatement::NestedBlock { block: typed_block }));
            }
        };
        Ok(())
    }

    pub fn analyze_expression<'a>(
        &'a self,
        expr: &Expression,
        symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a TypedExpression<'a>, SemanticAnalysisError> {
        match expr {
            Expression::Identifier { name: symbol_id } => {
                let symbol = symbol_table.lookup_by_name(*symbol_id);
                match symbol {
                    Some(symbol) => Ok(self.alloc(TypedExpression::Identifier {
                        symbol_id: symbol.id,
                        resolved_type: symbol.symbol_type,
                    })),
                    None => Err(SemanticAnalysisError::SymbolNotFound {
                        name: resolve_string_id(*symbol_id)
                            .expect("should be able to find string")
                            .to_owned(),
                    }),
                }
            }

            // Literals will never fail
            Expression::Literal(value) => Ok(self.alloc(TypedExpression::Literal {
                resolved_type: Type::of_literal(value),
                value: value.clone(),
            })),

            // Unary operators - can fail!
            Expression::Unary { operator, operand } => {
                let typed_operand = self.analyze_expression(operand, symbol_table)?;
                let operand_type = typed_operand.resolved_type();
                if (Self::unary_op_is_allowed(operator.clone(), operand_type)) {
                    Ok(self.alloc(TypedExpression::Unary {
                        resolved_type: operand_type,
                        operator: operator.clone(),
                        operand: typed_operand,
                    }))
                } else {
                    Err(SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                        operator: operator.clone(),
                        operand_type,
                    })
                }
            }

            // Binary operators - can fail!
            Expression::Binary {
                operator,
                left,
                right,
            } => {
                let typed_left = self.analyze_expression(left, symbol_table)?;
                let typed_right = self.analyze_expression(right, symbol_table)?;
                let left_type = typed_left.resolved_type();
                let right_type = typed_right.resolved_type();
                if Self::bin_op_is_allowed(operator.clone(), left_type, right_type) {
                    Ok(self.alloc(TypedExpression::Binary {
                        result_type: Self::type_of_operator(operator.clone(), left_type),
                        operator: operator.clone(),
                        operand_type: left_type,
                        left: typed_left,
                        right: typed_right,
                    }))
                } else {
                    Err(SemanticAnalysisError::CannotApplyBinaryOperatorToType {
                        operator: operator.clone(),
                        left_type,
                        right_type,
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

    fn type_of_operator(operator: BinaryOperator, left: Type) -> Type {
        match operator {
            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Rem
            | BinaryOperator::Exp
            | BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseOr
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseShl
            | BinaryOperator::BitwiseShr => left,
            BinaryOperator::Eq
            | BinaryOperator::Neq
            | BinaryOperator::Lt
            | BinaryOperator::Lte
            | BinaryOperator::Gt
            | BinaryOperator::Gte
            | BinaryOperator::And
            | BinaryOperator::Or => Type::Boolean,
        }
    }

    #[inline]
    fn alloc<T>(&self, value: T) -> &T {
        self.arena.alloc(value)
    }

    pub fn symbol_table<'a>(&'a self, parent: Option<&'a SymbolTable<'a>>) -> &'a SymbolTable<'a> {
        self.alloc(SymbolTable::new(&self.arena, parent))
    }
}

fn next_variable_index(symbol_table: &SymbolTable) -> VariableIndex {
    symbol_table.num_variables().into()
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
                    let ast_allocator = parser::AstAllocator::default();
                    let expression = parser::parse_as_expression(&ast_allocator, $source);
                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_expression(expression, symbol_table);
                    assert_eq!(
                        result
                            .expect("should have matched types correctly")
                            .to_string_with_symbol_table(symbol_table),
                        $typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::AstAllocator::default();
                    let expression = parser::parse_as_expression(&ast_allocator, $source);
                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_expression(expression, symbol_table);
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
        test_ok!(binary_compare, "1 > 2", "(>b 1i 2i)");
    }

    mod blocks {
        use super::*;

        macro_rules! test_ok {
            ($name: ident, $source: expr, $expected_typed_ast: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::AstAllocator::default();
                    let block = parser::parse_as_block(&ast_allocator, $source);

                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_block(block, symbol_table);

                    assert_eq!(
                        result
                            .expect("should have succeeded semantic analysis")
                            .to_string(),
                        $expected_typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::AstAllocator::default();
                    let block = parser::parse_as_block(&ast_allocator, $source);

                    let analyzer = SemanticAnalyzer::default();
                    let symbol_table = analyzer.symbol_table(None);
                    let result = analyzer.analyze_block(block, symbol_table);

                    assert_eq!(
                        result
                            .expect_err("should have failed semantic analysis")
                            .to_string(),
                        $expected_error
                    );
                }
            };
        }

        test_ok!(
            return_void,
            r"{
    return;
}",
            r"{ #0
  return;
}
"
        );
        test_ok!(
            return_expr,
            r"{
    return 42;
}",
            r"{ #0
  return 42i;
}
"
        );
        test_ok!(
            single_expression,
            r"{
    1 + 2;
}",
            r"{ #0
  (+i 1i 2i);
}
"
        );
        test_ok!(
            let_single,
            r"{
    let a = 42;
}",
            r"{ #0
  let a: int = 42i;
}
"
        );
        test_ok!(
            let_multiple,
            r"{
    let a = 42, b = true, c = 3.14;
}",
            r"{ #0
  let a: int = 42i;
  let b: boolean = true;
  let c: double = 3.14d;
}
"
        );
        test_ok!(
            let_can_redeclare_symbols,
            r"{
    let a = 42;
    let a = true;
}",
            r"{ #0
  let a: int = 42i;
  let a: boolean = true;
}
"
        );
        test_ok!(
            assignment_valid,
            r"{
    let a = 42;
    a = 43;
}",
            r"{ #0
  let a: int = 42i;
  a = 43i;
}
"
        );
        test_ok!(
            nested_block_basic,
            r"{
  {
    1 + 2;
  }
}",
            r"{ #0
  { #1
    (+i 1i 2i);
  }
}
"
        );
        test_ok!(
            nested_block_can_resolve_variables_declared_in_outer,
            r"{
  let a = 1;
  {
    a = 2;
  }
}",
            r"{ #0
  let a: int = 1i;
  { #1
    a = 2i;
  }
}
"
        );
        test_ok!(
            can_use_declared_variables_in_expressions,
            r"{
  let a = 1;
  a + 1;
}",
            r"{ #0
  let a: int = 1i;
  (+i a 1i);
}
"
        );

        test_ko!(
            assignment_symbol_not_found,
            r"{
    a = 1;
}",
            "symbol not found: \"a\""
        );
        test_ko!(
            assignment_type_mismatch,
            r"{
    let a = 42;
    a = false;
}",
            "invalid assignment to \"a\": symbol has type int, but expression has type boolean"
        );
        test_ko!(
            variables_declared_in_nested_block_cannot_be_accessed_in_outer,
            r"{
  {
    let a = 1;
  }
  a = 2;
}",
            "symbol not found: \"a\""
        );
        test_ko!(
            expression_symbol_not_found,
            r"{
    x;
}",
            "symbol not found: \"x\""
        );
    }

    mod modules {
        use super::*;

        macro_rules! test_ok {
            ($name: ident, $source: expr, $expected_typed_ast: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::AstAllocator::default();
                    let module = parser::parse(&ast_allocator, "test", $source);

                    let analyzer = SemanticAnalyzer::default();
                    let result = analyzer.analyze_module(module);

                    assert_eq!(
                        result
                            .expect("should have passed semantic analysis")
                            .to_string(),
                        $expected_typed_ast
                    );
                }
            };
        }

        macro_rules! test_ko {
            ($name: ident, $source: expr, $expected_error: expr) => {
                #[test]
                fn $name() {
                    let ast_allocator = parser::AstAllocator::default();
                    let module = parser::parse(&ast_allocator, "test", $source);

                    let analyzer = SemanticAnalyzer::default();
                    let result = analyzer.analyze_module(module);

                    assert_eq!(
                        result
                            .expect_err("should have failed semantic analysis")
                            .to_string(),
                        $expected_error
                    );
                }
            };
        }

        #[test]
        fn function_symbol_map_contains_arguments() {
            let ast_allocator = parser::AstAllocator::default();
            let module = parser::parse(
                &ast_allocator,
                "test",
                "fn inc(x: int) -> int { return 1 + x; }",
            );

            let analyzer = SemanticAnalyzer::default();
            let result = analyzer
                .analyze_module(module)
                .expect("should have passed semantic analysis");

            assert_eq!(1, result.functions.len());
            let fun = result.functions[0];
            assert_eq!(1, fun.symbol_table.len());
            let symbol = fun
                .symbol_table
                .lookup_by_name(parser::get_or_create_string("x"))
                .expect("should have found argument x");
            assert_eq!(Type::Int, symbol.symbol_type);
            assert_eq!(
                SymbolKind::Argument {
                    index: ArgumentIndex::from(0)
                },
                symbol.kind
            );
        }

        test_ok!(
            can_use_function_argument_in_expression,
            r"fn inc(x: int) -> int {
  return 1 + x;
}",
            r"module test

fn inc(
  x: int,
) -> int
{ #0
  return (+i 1i x);
}

"
        );
        test_ok!(
            can_assign_to_function_argument,
            r"fn inc(x: int) -> int {
  x = x + 1;
  return x;
}",
            r"module test

fn inc(
  x: int,
) -> int
{ #0
  let x: int = (+i x 1i);
  return x;
}

"
        );

        test_ko!(
            variable_not_found,
            r"fn a() {
    x;
}",
            "symbol not found: \"x\""
        );

        // TODO
        //         test_ko!(
        //             cannot_assign_to_function,
        //             r"fn a() {}
        //
        // fn b() {
        //   a = 1;
        // }",
        //             "symbol not found: \"x\""
        //         );

        // TODO: all return match expected type? here or in separate pass?
    }
}
