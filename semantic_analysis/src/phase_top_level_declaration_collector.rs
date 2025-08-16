use crate::ast_top_level_declaration::PhaseTopLevelDeclarationCollected;
use crate::semantic_analyzer::SemanticAnalysisError;
use parser::{
    AstAllocator, Block, Expression, FunctionDeclaration, FunctionSignature,
    FunctionSignaturesByName, IfElseBlock, IfStatement, LetInitializer, Module, PhaseParsed,
    Statement, WhileStatement,
};

pub(crate) struct TopLevelDeclarationCollector {}

impl<'a> TopLevelDeclarationCollector {
    pub(crate) fn analyze_module(
        allocator: &'a AstAllocator,
        module: &Module<PhaseParsed>,
    ) -> Result<&'a Module<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError> {
        let num_functions = module.function_signatures.len();

        let mut function_signatures = FunctionSignaturesByName::with_capacity(num_functions);
        let mut functions = allocator.new_bump_vec_with_capacity(num_functions);

        // First pass: map function signatures
        for function in module.functions.iter() {
            let return_type = function.signature.return_type;
            let mapped_function_signature = allocator.alloc(FunctionSignature {
                name: function.signature.name,
                return_type,
                arguments: allocator
                    .new_bump_vec_from_iter(function.signature.arguments.iter().cloned()),
            });

            function_signatures.insert(function.signature.name, mapped_function_signature);
        }

        // Second pass: map function calls
        for function in module.functions.iter() {
            functions.push(Self::map_function(
                allocator,
                &function_signatures,
                function,
            )?);
        }

        Ok(allocator.alloc({
            Module {
                name: module.name,
                functions,
                function_signatures,
            }
        }))
    }

    fn map_function(
        allocator: &'a AstAllocator,
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
        function: &FunctionDeclaration<PhaseParsed>,
    ) -> Result<
        &'a FunctionDeclaration<'a, PhaseTopLevelDeclarationCollected<'a>>,
        SemanticAnalysisError,
    > {
        let signature = Self::resolve_function_signature_for(function_signatures, function)?;

        Ok(allocator.alloc(FunctionDeclaration {
            signature,
            body: Self::map_block(allocator, function.body)?,
            symbol_table: (),
        }))
    }

    fn resolve_function_signature_for(
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
        function: &FunctionDeclaration<PhaseParsed>,
    ) -> Result<
        &'a FunctionSignature<'a, PhaseTopLevelDeclarationCollected<'a>>,
        SemanticAnalysisError,
    > {
        function_signatures
            .get(&function.signature.name)
            .cloned()
            .ok_or_else(|| SemanticAnalysisError::InternalError {
                message: "function signature must exist as we just put it there".to_string(),
            })
    }

    fn map_block(
        allocator: &'a AstAllocator,
        block: &Block<PhaseParsed>,
    ) -> Result<&'a Block<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError> {
        let mapped_statements = allocator.new_bump_vec_from_iter_result(
            block
                .statements
                .iter()
                .map(|statement| Self::map_statement(allocator, statement)),
        )?;
        Ok(allocator.alloc(Block {
            id: block.id,
            statements: mapped_statements,
            symbol_table: (),
        }))
    }

    fn map_statement(
        allocator: &'a AstAllocator,
        statement: &Statement<PhaseParsed>,
    ) -> Result<&'a Statement<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError>
    {
        Ok(allocator.alloc(match statement {
            Statement::Let { initializers } => {
                let mapped_initializers = allocator.new_bump_vec_from_iter_result(
                    initializers.iter().map(|initializer| {
                        let value = Self::map_expression(allocator, initializer.value);
                        value.map(|value| LetInitializer {
                            variable: initializer.variable,
                            value,
                        })
                    }),
                )?;
                Statement::Let {
                    initializers: mapped_initializers,
                }
            }
            Statement::Assignment { target, expression } => Statement::Assignment {
                target: *target,
                expression: Self::map_expression(allocator, expression)?,
            },
            Statement::Return { expression } => Statement::Return {
                expression: expression
                    .map(|e| Self::map_expression(allocator, e))
                    .transpose()?,
            },
            Statement::Expression { expression } => Statement::Expression {
                expression: Self::map_expression(allocator, expression)?,
            },
            Statement::NestedBlock { block } => Statement::NestedBlock {
                block: Self::map_block(allocator, block)?,
            },
            Statement::If(if_statement) => {
                let mapped_condition = Self::map_expression(allocator, if_statement.condition)?;
                let mapped_then_block = Self::map_block(allocator, if_statement.then_block)?;
                let mapped_else_block = if_statement
                    .else_block
                    .map(|else_block| Self::map_if_else_block(allocator, else_block))
                    .transpose()?;

                let mapped_if_statement = allocator.alloc(IfStatement {
                    condition: mapped_condition,
                    then_block: mapped_then_block,
                    else_block: mapped_else_block,
                });
                Statement::If(mapped_if_statement)
            }
            Statement::While(while_statement) => {
                let mapped_condition = Self::map_expression(allocator, while_statement.condition)?;
                let mapped_body = Self::map_block(allocator, while_statement.body)?;

                let mapped_while_statement = allocator.alloc(WhileStatement {
                    condition: mapped_condition,
                    body: mapped_body,
                });
                Statement::While(mapped_while_statement)
            }
            Statement::Loop { body } => {
                let mapped_body = Self::map_block(allocator, body)?;
                Statement::Loop { body: mapped_body }
            }
            Statement::Break => Statement::Break,
            Statement::Continue => Statement::Continue,
        }))
    }

    fn map_expression(
        allocator: &'a AstAllocator,
        expression: &Expression<PhaseParsed>,
    ) -> Result<&'a Expression<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError>
    {
        Ok(allocator.alloc(match expression {
            Expression::Identifier {
                resolved_type,
                name,
            } => Expression::Identifier {
                resolved_type: *resolved_type,
                name: *name,
            },
            Expression::Literal {
                value,
                resolved_type,
            } => Expression::Literal {
                value: value.clone(),
                resolved_type: *resolved_type,
            },
            Expression::Unary {
                operator,
                operand,
                resolved_type,
            } => Expression::Unary {
                operator: operator.clone(),
                operand: Self::map_expression(allocator, operand)?,
                resolved_type: *resolved_type,
            },
            Expression::Binary {
                result_type,
                operator,
                operand_type,
                left,
                right,
            } => Expression::Binary {
                operator: operator.clone(),
                operand_type: *operand_type,
                left: Self::map_expression(allocator, left)?,
                right: Self::map_expression(allocator, right)?,
                result_type: *result_type,
            },
            Expression::FunctionCall { name, args, .. } => {
                let mapped_args = allocator.new_bump_vec_from_iter_result(
                    args.iter().map(|arg| Self::map_expression(allocator, arg)),
                )?;
                Expression::FunctionCall {
                    name: *name,
                    args: mapped_args,
                    return_type: (),
                }
            }
        }))
    }

    fn map_if_else_block(
        allocator: &'a AstAllocator,
        else_block: &IfElseBlock<PhaseParsed>,
    ) -> Result<&'a IfElseBlock<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError>
    {
        Ok(allocator.alloc(match else_block {
            IfElseBlock::Block(block) => IfElseBlock::Block(Self::map_block(allocator, block)?),
            IfElseBlock::If(if_statement) => {
                let mapped_condition = Self::map_expression(allocator, if_statement.condition)?;
                let mapped_then_block = Self::map_block(allocator, if_statement.then_block)?;
                let mapped_else_block = if let Some(else_block) = if_statement.else_block {
                    Some(Self::map_if_else_block(allocator, else_block)?)
                } else {
                    None
                };

                let mapped_if_statement = allocator.alloc(IfStatement {
                    condition: mapped_condition,
                    then_block: mapped_then_block,
                    else_block: mapped_else_block,
                });
                IfElseBlock::If(mapped_if_statement)
            }
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::phase_top_level_declaration_collector::TopLevelDeclarationCollector;
    use kigiri_memory::intern_string;
    use parser::{AstAllocator, Expression, FunctionArgument, FunctionSignature, Statement};

    #[test]
    fn function_call_resolved() {
        const SOURCE: &str = r"
fn main() {
    add(1, 2);
}

fn add(a: int, b: int) -> int {
    return a + b;
}
";

        let ast_allocator = parser::ParsedAstAllocator::default();
        let module = parser::parse(&ast_allocator, "test", SOURCE).expect("parse should succeed");

        let allocator = AstAllocator::default();
        let analyzed = TopLevelDeclarationCollector::analyze_module(&allocator, module)
            .expect("should have passed semantic analysis");

        assert_eq!(2, analyzed.function_signatures.len());
        assert_eq!(
            **analyzed
                .function_signatures
                .get(&intern_string("main"))
                .expect("should find main"),
            FunctionSignature {
                name: intern_string("main"),
                return_type: None,
                arguments: allocator.new_bump_vec(),
            }
        );
        let add_signature = analyzed
            .function_signatures
            .get(&intern_string("add"))
            .expect("should find add");
        assert_eq!(
            **add_signature,
            FunctionSignature {
                name: intern_string("add"),
                return_type: Some(intern_string("int")),
                arguments: allocator.new_bump_vec_from_iter(vec![
                    FunctionArgument {
                        name: intern_string("a"),
                        argument_type: intern_string("int"),
                    },
                    FunctionArgument {
                        name: intern_string("b"),
                        argument_type: intern_string("int"),
                    }
                ]),
            }
        );

        let main = analyzed
            .functions
            .first()
            .expect("should have main function");
        let expression_statement = main
            .body
            .statements
            .first()
            .expect("should find the return statement");
        let expression = *match expression_statement {
            Statement::Expression { expression } => expression,
            _ => panic!("Expected a return statement"),
        };
        let Expression::FunctionCall { name, args, .. } = expression else {
            panic!("Expected a function call expression")
        };
        assert_eq!(*name, intern_string("add"));
        assert_eq!(args.len(), 2);
        assert_eq!(
            *args[0],
            Expression::Literal {
                value: parser::LiteralValue::Integer(1),
                resolved_type: (),
            }
        );
        assert_eq!(
            *args[1],
            Expression::Literal {
                value: parser::LiteralValue::Integer(2),
                resolved_type: (),
            }
        );
    }
}
