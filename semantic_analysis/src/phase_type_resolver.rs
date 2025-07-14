use crate::ast_top_level_declaration::PhaseTopLevelDeclarationCollected;
use crate::semantic_analyzer::SemanticAnalysisError;
use crate::{
    resolved_type, ArgumentIndex, PhaseTypeResolved, SymbolId, SymbolKind, SymbolTable, Type,
};
use bumpalo::collections::Vec as BumpVec;
use parser::{
    resolve_string_id, AstAllocator, BinaryOperator, Block, Expression, FunctionDeclaration,
    FunctionSignature, FunctionSignaturesByName, LetInitializer, Module, Statement, UnaryOperator,
};

/// Infers and checks types
pub(crate) struct TypeResolver {}

impl<'a> TypeResolver {
    pub(crate) fn analyze_module(
        allocator: &'a AstAllocator,
        module: &Module<PhaseTopLevelDeclarationCollected>,
    ) -> Result<&'a Module<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        let global_symbol_table = SymbolTable::new(allocator, None);

        // First pass: add all functions to the global symbol table
        for function in module.functions.iter() {
            let return_type = function
                .signature
                .return_type
                .map(Type::parse)
                .transpose()?
                .unwrap_or(Type::Int); // TODO: proper void type handling

            global_symbol_table.add_symbol(
                allocator,
                function.signature.name,
                return_type,
                SymbolKind::Function,
            );
        }

        let mut function_signatures =
            FunctionSignaturesByName::with_capacity(module.function_signatures.len());
        let mut functions = allocator.new_bump_vec_with_capacity(module.functions.len());

        // Second pass: analyze functions with access to the global symbol table
        for function in module.functions.iter() {
            let function = Self::analyze_function(allocator, function, global_symbol_table)?;
            functions.push(function);
            function_signatures.insert(function.signature.name, function.signature);
        }

        Ok(allocator.alloc({
            Module {
                name: module.name,
                functions,
                function_signatures,
            }
        }))
    }

    fn analyze_function(
        allocator: &'a AstAllocator,
        function: &FunctionDeclaration<PhaseTopLevelDeclarationCollected>,
        global_symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a FunctionDeclaration<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        let symbol_table = SymbolTable::new(allocator, Some(global_symbol_table));

        let return_type = function
            .signature
            .return_type
            .map(Type::parse)
            .transpose()?;

        let arguments = function
            .signature
            .arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                let arg_type = Type::parse(argument.arg_type);
                arg_type.map(|arg_type| {
                    symbol_table.add_symbol(
                        allocator,
                        argument.name,
                        arg_type,
                        SymbolKind::Argument {
                            index: ArgumentIndex::from(index as u32),
                        },
                    )
                })
            })
            .collect::<Result<Vec<SymbolId>, SemanticAnalysisError>>()?;
        let arguments = allocator.new_bump_vec_from_iter(arguments.iter().cloned());

        let signature = allocator.alloc(FunctionSignature {
            name: function.signature.name,
            return_type,
            arguments,
        });

        let body = Self::analyze_block(allocator, function.body, symbol_table)?;

        Ok(allocator.alloc(FunctionDeclaration {
            signature,
            body,
            symbol_table,
        }))
    }

    pub(crate) fn analyze_block(
        allocator: &'a AstAllocator,
        block: &Block<PhaseTopLevelDeclarationCollected>,
        parent_symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a Block<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        let mut statements = allocator.new_bump_vec_with_capacity(block.statements.len());
        for statement in &block.statements {
            Self::analyze_statement(allocator, statement, &mut statements, parent_symbol_table)?;
        }
        Ok(allocator.alloc(Block {
            id: block.id,
            statements,
            symbol_table: parent_symbol_table,
        }))
    }

    fn analyze_statement(
        allocator: &'a AstAllocator,
        statement: &Statement<PhaseTopLevelDeclarationCollected>,
        statements: &mut BumpVec<'a, &'a Statement<'a, PhaseTypeResolved<'a>>>,
        symbol_table: &'a SymbolTable<'a>,
    ) -> Result<(), SemanticAnalysisError> {
        match statement {
            Statement::Let { initializers } => {
                let mut typed_initializers = allocator.new_bump_vec();

                for initializer in initializers {
                    let value =
                        Self::analyze_expression(allocator, initializer.value, symbol_table)?;

                    let resolved_type = if let Some(rt) = resolved_type(value) {
                        rt
                    } else {
                        return Err(SemanticAnalysisError::CannotAssignVoidValue {
                            name: resolve_string_id(initializer.variable)
                                .expect("let variable name")
                                .to_owned(),
                        });
                    };

                    let variable = symbol_table.add_symbol(
                        allocator,
                        initializer.variable,
                        resolved_type,
                        SymbolKind::Variable {
                            index: symbol_table.next_variable_index(),
                        },
                    );
                    typed_initializers.push(LetInitializer { variable, value });
                }

                statements.push(allocator.alloc(Statement::Let {
                    initializers: typed_initializers,
                }))
            }
            Statement::Assignment {
                target: name,
                expression,
            } => {
                let symbol_name = resolve_string_id(*name)
                    .expect("should be able to find string")
                    .to_owned();

                let symbol = symbol_table.lookup_by_name(*name);

                match symbol {
                    None => {
                        return Err(SemanticAnalysisError::SymbolNotFound { name: symbol_name });
                    }
                    Some(symbol) => {
                        let value = Self::analyze_expression(allocator, expression, symbol_table)?;

                        let expression_type = resolved_type(value).ok_or(
                            SemanticAnalysisError::CannotAssignVoidValue {
                                name: resolve_string_id(symbol.name)
                                    .expect("assignment target")
                                    .to_owned(),
                            },
                        )?;

                        if expression_type != symbol.symbol_type {
                            return Err(SemanticAnalysisError::MismatchedAssignmentType {
                                symbol_name,
                                symbol_type: symbol.symbol_type,
                                expression_type,
                            });
                        }

                        match symbol.kind {
                            SymbolKind::Function => {
                                return Err(SemanticAnalysisError::CannotAssignToFunction {
                                    name: symbol_name,
                                });
                            }
                            SymbolKind::Variable { .. } => {
                                statements.push(allocator.alloc(Statement::Assignment {
                                    target: symbol.id,
                                    expression: value,
                                }))
                            }
                            SymbolKind::Argument { index } => {
                                // We actually need to create a new variable and assign to that
                                // one, because LLVM (and thus our IR) does not allow reassigning
                                // a function argument.
                                let new_variable = symbol_table.add_symbol(
                                    allocator,
                                    *name,
                                    expression_type,
                                    SymbolKind::Variable {
                                        index: symbol_table.next_variable_index(),
                                    },
                                );
                                statements.push(allocator.alloc(Statement::Let {
                                    initializers: allocator.new_bump_vec_from_iter([
                                        LetInitializer {
                                            variable: new_variable,
                                            value,
                                        },
                                    ]),
                                }));
                            }
                        }
                    }
                }
            }
            Statement::Return { expression } => {
                let expression = expression
                    .map(|expr| Self::analyze_expression(allocator, expr, symbol_table))
                    .transpose()?;
                statements.push(allocator.alloc(Statement::Return { expression }));
            }
            Statement::Expression { expression } => {
                let typed_expression =
                    Self::analyze_expression(allocator, expression, symbol_table)?;
                statements.push(allocator.alloc(Statement::Expression {
                    expression: typed_expression,
                }))
            }
            Statement::NestedBlock { block } => {
                let nested_symbol_table = SymbolTable::new(allocator, Some(symbol_table));
                let typed_block = Self::analyze_block(allocator, block, nested_symbol_table)?;
                statements.push(allocator.alloc(Statement::NestedBlock { block: typed_block }));
            }
        };
        Ok(())
    }

    pub(crate) fn analyze_expression(
        allocator: &'a AstAllocator,
        expr: &Expression<PhaseTopLevelDeclarationCollected>,
        symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a Expression<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        match expr {
            Expression::Identifier {
                name: symbol_id, ..
            } => {
                let symbol = symbol_table.lookup_by_name(*symbol_id);
                match symbol {
                    Some(symbol) => {
                        // Only allow variables and arguments in identifier expressions, not functions
                        match symbol.kind {
                            SymbolKind::Variable { .. } | SymbolKind::Argument { .. } => {
                                Ok(allocator.alloc(Expression::Identifier {
                                    name: symbol.id,
                                    resolved_type: Some(symbol.symbol_type),
                                }))
                            }
                            // TODO: make a different error
                            SymbolKind::Function => Err(SemanticAnalysisError::SymbolNotFound {
                                name: resolve_string_id(*symbol_id)
                                    .expect("should be able to find string")
                                    .to_owned(),
                            }),
                        }
                    }
                    None => Err(SemanticAnalysisError::SymbolNotFound {
                        name: resolve_string_id(*symbol_id)
                            .expect("should be able to find string")
                            .to_owned(),
                    }),
                }
            }

            Expression::FunctionCall {
                name,
                args,
                signature,
            } => {
                let function_symbol = symbol_table.lookup_by_name(*name);
                let function_symbol = match function_symbol {
                    Some(symbol) => match symbol.kind {
                        SymbolKind::Function => symbol,
                        _ => {
                            return Err(SemanticAnalysisError::FunctionNotFound {
                                function_name: resolve_string_id(*name)
                                    .expect("should be able to find string")
                                    .to_owned(),
                            });
                        }
                    },
                    None => {
                        return Err(SemanticAnalysisError::FunctionNotFound {
                            function_name: resolve_string_id(*name)
                                .expect("should be able to find string")
                                .to_owned(),
                        });
                    }
                };

                // Type-check all arguments
                let typed_args = args
                    .iter()
                    .map(|arg| Self::analyze_expression(allocator, arg, symbol_table))
                    .collect::<Result<Vec<_>, _>>()?;
                let typed_args = allocator.new_bump_vec_from_iter(typed_args.into_iter());

                // For now, create a minimal typed signature with empty arguments
                // TODO: properly handle function signature conversion when argument validation is needed
                let typed_signature = allocator.alloc(FunctionSignature {
                    name: signature.name,
                    return_type: signature.return_type.map(Type::parse).transpose()?,
                    arguments: allocator.new_bump_vec(), // Empty for now
                });

                Ok(allocator.alloc(Expression::FunctionCall {
                    name: function_symbol.id,
                    args: typed_args,
                    signature: typed_signature,
                }))
            }

            // Literals will never fail
            Expression::Literal { value, .. } => Ok(allocator.alloc(Expression::Literal {
                resolved_type: Some(Type::of_literal(value)),
                value: value.clone(),
            })),

            // Unary operators - can fail!
            Expression::Unary {
                operator, operand, ..
            } => {
                let typed_operand = Self::analyze_expression(allocator, operand, symbol_table)?;
                let operand_type = resolved_type(typed_operand);

                let operand_type =
                    operand_type.ok_or(SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                        operator: operator.clone(),
                        operand_type: "void".to_string(),
                    })?;

                if (Self::unary_op_is_allowed(operator.clone(), operand_type)) {
                    Ok(allocator.alloc(Expression::Unary {
                        resolved_type: operand_type,
                        operator: operator.clone(),
                        operand: typed_operand,
                    }))
                } else {
                    Err(SemanticAnalysisError::CannotApplyUnaryOperatorToType {
                        operator: operator.clone(),
                        operand_type: operand_type.to_string(),
                    })
                }
            }

            // Binary operators - can fail!
            Expression::Binary {
                operator,
                left,
                right,
                ..
            } => {
                let typed_left = Self::analyze_expression(allocator, left, symbol_table)?;
                let typed_right = Self::analyze_expression(allocator, right, symbol_table)?;
                let left_type = resolved_type(typed_left);
                let right_type = resolved_type(typed_right);

                let left_type = left_type.ok_or_else(|| {
                    SemanticAnalysisError::CannotApplyBinaryOperatorToType {
                        operator: operator.clone(),
                        left_type: "void".to_owned(),
                        right_type: Type::name(right_type),
                    }
                })?;
                let right_type = right_type.ok_or_else(|| {
                    SemanticAnalysisError::CannotApplyBinaryOperatorToType {
                        operator: operator.clone(),
                        left_type: left_type.to_string(),
                        right_type: "void".to_owned(),
                    }
                })?;

                if Self::bin_op_is_allowed(operator.clone(), left_type, right_type) {
                    Ok(allocator.alloc(Expression::Binary {
                        result_type: Self::type_of_operator(operator.clone(), left_type),
                        operator: operator.clone(),
                        operand_type: left_type,
                        left: typed_left,
                        right: typed_right,
                    }))
                } else {
                    Err(SemanticAnalysisError::CannotApplyBinaryOperatorToType {
                        operator: operator.clone(),
                        left_type: left_type.to_string(),
                        right_type: right_type.to_string(),
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
}
