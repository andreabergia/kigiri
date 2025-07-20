use crate::ast_top_level_declaration::PhaseTopLevelDeclarationCollected;
use crate::semantic_analyzer::SemanticAnalysisError;
use crate::{ArgumentIndex, PhaseTypeResolved, SymbolKind, SymbolTable, Type, resolved_type};
use bumpalo::collections::Vec as BumpVec;
use parser::{
    AstAllocator, BinaryOperator, Block, Expression, FunctionDeclaration, FunctionSignature,
    FunctionSignaturesByName, IfElseBlock, IfStatement, LetInitializer, Module, Statement,
    StringId, UnaryOperator, resolve_string_id,
};
use std::cmp::Ordering;
use std::collections::HashMap;

/// Infers and checks types
pub(crate) struct TypeResolver {}

struct MappedFunctionSignature<'a> {
    signature: &'a FunctionSignature<'a, PhaseTypeResolved<'a>>,
    symbol_table: &'a SymbolTable<'a>,
}

type MappedFunctionSignatures<'a> = HashMap<StringId, MappedFunctionSignature<'a>>;

impl<'a> TypeResolver {
    pub(crate) fn analyze_module(
        allocator: &'a AstAllocator,
        module: &Module<PhaseTopLevelDeclarationCollected>,
    ) -> Result<&'a Module<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        // First pass: add all functions to the global symbol table
        // Note that we need to also map the signatures here
        let num_functions = module.function_signatures.len();
        let global_symbol_table = SymbolTable::new_global(allocator, num_functions);
        let mut mapped_signatures: MappedFunctionSignatures<'a> =
            HashMap::with_capacity(num_functions);
        let mut function_signatures =
            FunctionSignaturesByName::with_capacity(module.function_signatures.len());

        for function in module.functions.iter() {
            let mapped =
                Self::map_function_signature(allocator, function.signature, global_symbol_table)?;

            global_symbol_table.add_symbol(
                allocator,
                mapped.signature.name,
                SymbolKind::Function {
                    signature: mapped.signature,
                },
            );

            function_signatures.insert(mapped.signature.name, mapped.signature);
            mapped_signatures.insert(mapped.signature.name, mapped);
        }

        // Second pass: analyze functions with access to the global symbol table
        let mut functions = allocator.new_bump_vec_with_capacity(module.functions.len());
        for function in module.functions.iter() {
            let function = Self::analyze_function(
                allocator,
                function,
                global_symbol_table,
                &mapped_signatures,
            )?;
            functions.push(function);
        }

        Ok(allocator.alloc({
            Module {
                name: module.name,
                functions,
                function_signatures,
            }
        }))
    }

    fn map_function_signature(
        allocator: &'a AstAllocator,
        function_signature: &FunctionSignature<PhaseTopLevelDeclarationCollected>,
        global_symbol_table: &'a SymbolTable<'a>,
    ) -> Result<MappedFunctionSignature<'a>, SemanticAnalysisError> {
        let symbol_table = SymbolTable::new(allocator, Some(global_symbol_table));

        let return_type = function_signature
            .return_type
            .map(Type::parse)
            .transpose()?;

        let arguments = function_signature
            .arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                let arg_type = Type::parse(argument.argument_type);
                arg_type.map(|argument_type| {
                    symbol_table
                        .add_symbol(
                            allocator,
                            argument.name,
                            SymbolKind::Argument {
                                index: ArgumentIndex::from(index as u32),
                                argument_type,
                            },
                        )
                        .symbol
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let arguments = allocator.new_bump_vec_from_iter(arguments.iter().cloned());

        let signature = allocator.alloc(FunctionSignature {
            name: function_signature.name,
            return_type,
            arguments,
        });
        Ok(MappedFunctionSignature {
            signature,
            symbol_table,
        })
    }

    fn analyze_function(
        allocator: &'a AstAllocator,
        function: &FunctionDeclaration<PhaseTopLevelDeclarationCollected>,
        global_symbol_table: &'a SymbolTable<'a>,
        mapped_signatures: &MappedFunctionSignatures<'a>,
    ) -> Result<&'a FunctionDeclaration<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        let MappedFunctionSignature {
            signature,
            symbol_table,
        } = mapped_signatures
            .get(&function.signature.name)
            .expect("must be able to find signature since we just built it");

        let body = Self::analyze_block(allocator, function.body, symbol_table)?;

        Ok(allocator.alloc(FunctionDeclaration {
            signature,
            body,
            symbol_table,
        }))
    }

    fn analyze_block(
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

                    let Some(variable_type) = resolved_type(value) else {
                        return Err(SemanticAnalysisError::CannotAssignVoidValue {
                            name: resolve_string_id(initializer.variable)
                                .expect("let variable name")
                                .to_owned(),
                        });
                    };

                    let variable = symbol_table
                        .add_symbol(
                            allocator,
                            initializer.variable,
                            SymbolKind::Variable {
                                index: symbol_table.next_variable_index(),
                                variable_type,
                            },
                        )
                        .id;
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

                        match symbol.kind {
                            SymbolKind::Function { .. } => {
                                return Err(SemanticAnalysisError::CannotAssignToFunction {
                                    name: symbol_name,
                                });
                            }
                            SymbolKind::Variable { variable_type, .. } => {
                                if expression_type != variable_type {
                                    return Err(SemanticAnalysisError::MismatchedAssignmentType {
                                        symbol_name,
                                        symbol_type: variable_type,
                                        expression_type,
                                    });
                                }

                                statements.push(allocator.alloc(Statement::Assignment {
                                    target: symbol.id,
                                    expression: value,
                                }))
                            }
                            SymbolKind::Argument {
                                argument_type,
                                index,
                            } => {
                                if expression_type != argument_type {
                                    return Err(SemanticAnalysisError::MismatchedAssignmentType {
                                        symbol_name,
                                        symbol_type: argument_type,
                                        expression_type,
                                    });
                                }

                                // We actually need to create a new variable and assign to that
                                // one, because LLVM (and thus our IR) does not allow reassigning
                                // a function argument.
                                let new_variable = symbol_table
                                    .add_symbol(
                                        allocator,
                                        *name,
                                        SymbolKind::Variable {
                                            index: symbol_table.next_variable_index(),
                                            variable_type: argument_type,
                                        },
                                    )
                                    .id;
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
            Statement::If(if_statement) => {
                // Type check the condition - it must be a boolean expression
                let typed_condition =
                    Self::analyze_expression(allocator, if_statement.condition, symbol_table)?;
                let condition_type = resolved_type(typed_condition);

                match condition_type {
                    Some(Type::Bool) => {
                        // Condition is valid, continue with blocks
                    }
                    Some(other_type) => {
                        return Err(SemanticAnalysisError::IfConditionMustBeBool {
                            actual_type: other_type.to_string(),
                        });
                    }
                    None => {
                        return Err(SemanticAnalysisError::IfConditionMustBeBool {
                            actual_type: "void".to_string(),
                        });
                    }
                }

                // Type check the then block
                let then_symbol_table = SymbolTable::new(allocator, Some(symbol_table));
                let typed_then_block =
                    Self::analyze_block(allocator, if_statement.then_block, then_symbol_table)?;

                // Type check the else block if present
                let typed_else_block = if let Some(else_block) = if_statement.else_block {
                    Some(Self::analyze_if_else_block(
                        allocator,
                        else_block,
                        symbol_table,
                    )?)
                } else {
                    None
                };

                let typed_if_statement = allocator.alloc(IfStatement {
                    condition: typed_condition,
                    then_block: typed_then_block,
                    else_block: typed_else_block,
                });

                statements.push(allocator.alloc(Statement::If(typed_if_statement)));
            }
        };
        Ok(())
    }

    fn analyze_if_else_block(
        allocator: &'a AstAllocator,
        else_block: &IfElseBlock<PhaseTopLevelDeclarationCollected>,
        symbol_table: &'a SymbolTable<'a>,
    ) -> Result<&'a IfElseBlock<'a, PhaseTypeResolved<'a>>, SemanticAnalysisError> {
        match else_block {
            IfElseBlock::Block(block) => {
                let else_symbol_table = SymbolTable::new(allocator, Some(symbol_table));
                let typed_block = Self::analyze_block(allocator, block, else_symbol_table)?;
                Ok(allocator.alloc(IfElseBlock::Block(typed_block)))
            }
            IfElseBlock::If(if_statement) => {
                // Type check the condition - it must be a boolean expression
                let analyzed_condition =
                    Self::analyze_expression(allocator, if_statement.condition, symbol_table)?;
                let condition_type = resolved_type(analyzed_condition);

                match condition_type {
                    Some(Type::Bool) => {
                        // Condition is valid, continue with blocks
                    }
                    Some(other_type) => {
                        return Err(SemanticAnalysisError::IfConditionMustBeBool {
                            actual_type: other_type.to_string(),
                        });
                    }
                    None => {
                        return Err(SemanticAnalysisError::IfConditionMustBeBool {
                            actual_type: "void".to_string(),
                        });
                    }
                }

                let analyzed_then_block =
                    Self::analyze_block(allocator, if_statement.then_block, symbol_table)?;
                let analyzed_else_block = if let Some(else_block) = if_statement.else_block {
                    Some(Self::analyze_if_else_block(
                        allocator,
                        else_block,
                        symbol_table,
                    )?)
                } else {
                    None
                };

                let analyzed_if_statement = allocator.alloc(IfStatement {
                    condition: analyzed_condition,
                    then_block: analyzed_then_block,
                    else_block: analyzed_else_block,
                });
                Ok(allocator.alloc(IfElseBlock::If(analyzed_if_statement)))
            }
        }
    }

    fn analyze_expression(
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
                            SymbolKind::Variable {
                                variable_type: resolved_type,
                                ..
                            }
                            | SymbolKind::Argument {
                                argument_type: resolved_type,
                                ..
                            } => Ok(allocator.alloc(Expression::Identifier {
                                name: symbol.id,
                                resolved_type: Some(resolved_type),
                            })),
                            // TODO: allow eventually assigning variables of function type
                            SymbolKind::Function { .. } => {
                                Err(SemanticAnalysisError::SymbolNotFound {
                                    name: resolve_string_id(*symbol_id)
                                        .expect("should be able to find string")
                                        .to_owned(),
                                })
                            }
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
                return_type,
            } => {
                let function_symbol = symbol_table.lookup_by_name(*name);
                let Some(function_symbol) = function_symbol else {
                    return Err(SemanticAnalysisError::FunctionNotFound {
                        function_name: resolve_string_id(*name)
                            .expect("should be able to find string")
                            .to_owned(),
                    });
                };
                let SymbolKind::Function { signature, .. } = function_symbol.kind else {
                    return Err(SemanticAnalysisError::NotAFunction {
                        name: resolve_string_id(*name)
                            .expect("should be able to find string")
                            .to_owned(),
                    });
                };

                let expected_arg_count = signature.arguments.len();
                let actual_arg_count = args.len();

                match actual_arg_count.cmp(&expected_arg_count) {
                    Ordering::Less => Err(SemanticAnalysisError::ArgumentCountMismatchTooFew {
                        function_name: resolve_string_id(*name)
                            .expect("should be able to find string")
                            .to_owned(),
                        expected: expected_arg_count,
                        found: actual_arg_count,
                    }),
                    Ordering::Greater => Err(SemanticAnalysisError::ArgumentCountMismatchTooMany {
                        function_name: resolve_string_id(*name)
                            .expect("should be able to find string")
                            .to_owned(),
                        expected: expected_arg_count,
                        found: actual_arg_count,
                    }),
                    Ordering::Equal => {
                        // Type-check all arguments
                        let actual_arguments = args
                            .iter()
                            .map(|arg| Self::analyze_expression(allocator, arg, symbol_table))
                            .collect::<Result<Vec<_>, _>>()?;

                        // Check each argument type against the expected type
                        for (argument_index, (typed_arg, expected_symbol)) in actual_arguments
                            .iter()
                            .zip(signature.arguments.iter())
                            .enumerate()
                        {
                            let actual_type = resolved_type(typed_arg);

                            let expected_type = expected_symbol
                                .symbol_type()
                                .expect("Function argument should have a type");

                            if let Some(actual_type) = actual_type {
                                if actual_type != expected_type {
                                    return Err(SemanticAnalysisError::ArgumentTypeMismatch {
                                        function_name: resolve_string_id(*name)
                                            .expect("should be able to find string")
                                            .to_owned(),
                                        argument_index,
                                        parameter_name: resolve_string_id(expected_symbol.name)
                                            .expect("should be able to find string")
                                            .to_owned(),
                                        expected_type,
                                        actual_type: actual_type.to_string(),
                                    });
                                }
                            } else {
                                // void type cannot be passed as argument
                                return Err(SemanticAnalysisError::ArgumentTypeMismatch {
                                    function_name: resolve_string_id(*name)
                                        .expect("should be able to find string")
                                        .to_owned(),
                                    argument_index,
                                    parameter_name: resolve_string_id(expected_symbol.name)
                                        .expect("should be able to find string")
                                        .to_owned(),
                                    expected_type,
                                    actual_type: "void".to_string(),
                                });
                            }
                        }

                        let typed_args = allocator.new_bump_vec_from_iter(actual_arguments);

                        Ok(allocator.alloc(Expression::FunctionCall {
                            name: function_symbol.id,
                            args: typed_args,
                            return_type: signature.return_type,
                        }))
                    }
                }
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
            UnaryOperator::Not => operand_type == Type::Bool,
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
                left_type == right_type && left_type == Type::Bool
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
            | BinaryOperator::Or => Type::Bool,
        }
    }
}
