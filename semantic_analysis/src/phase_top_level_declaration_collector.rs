use crate::ast_top_level_declaration::PhaseTopLevelDeclarationCollected;
use crate::semantic_analyzer::SemanticAnalysisError;
use crate::Type;
use parser::{
    resolve_string_id, AstAllocator, Block, Expression, FunctionDeclaration,
    FunctionSignature, FunctionSignaturesByName, LetInitializer, Module, PhaseParsed, Statement,
    StringId,
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
            let return_type = return_type.map(Type::parse).transpose()?;
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
        let signature = Self::resolve_function_signature_for(function_signatures, function);

        Ok(allocator.alloc(FunctionDeclaration {
            signature,
            body: Self::map_block(allocator, function_signatures, function.body)?,
            symbol_table: (),
        }))
    }

    fn resolve_function_signature_for(
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
        function: &FunctionDeclaration<PhaseParsed>,
    ) -> &'a FunctionSignature<'a, PhaseTopLevelDeclarationCollected<'a>> {
        function_signatures
            .get(&function.signature.name)
            .expect("function signature must exist as we just put it there")
    }

    fn map_block(
        allocator: &'a AstAllocator,
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
        block: &Block<PhaseParsed>,
    ) -> Result<&'a Block<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError> {
        let mapped_statements = allocator.new_bump_vec_from_iter_result(
            block
                .statements
                .iter()
                .map(|statement| Self::map_statement(allocator, function_signatures, statement)),
        )?;
        Ok(allocator.alloc(Block {
            id: block.id,
            statements: mapped_statements,
            symbol_table: (),
        }))
    }

    fn map_statement(
        allocator: &'a AstAllocator,
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
        statement: &Statement<PhaseParsed>,
    ) -> Result<&'a Statement<'a, PhaseTopLevelDeclarationCollected<'a>>, SemanticAnalysisError>
    {
        Ok(allocator.alloc(match statement {
            Statement::Let { initializers } => {
                let mapped_initializers = allocator.new_bump_vec_from_iter_result(
                    initializers.iter().map(|initializer| {
                        let value =
                            Self::map_expression(allocator, function_signatures, initializer.value);
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
                expression: Self::map_expression(allocator, function_signatures, expression)?,
            },
            Statement::Return { expression } => Statement::Return {
                expression: expression
                    .map(|e| Self::map_expression(allocator, function_signatures, e))
                    .transpose()?,
            },
            Statement::Expression { expression } => Statement::Expression {
                expression: Self::map_expression(allocator, function_signatures, expression)?,
            },
            Statement::NestedBlock { block } => Statement::NestedBlock {
                block: Self::map_block(allocator, function_signatures, block)?,
            },
        }))
    }

    fn map_expression(
        allocator: &'a AstAllocator,
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
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
                operand: Self::map_expression(allocator, function_signatures, operand)?,
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
                left: Self::map_expression(allocator, function_signatures, left)?,
                right: Self::map_expression(allocator, function_signatures, right)?,
                result_type: *result_type,
            },
            Expression::FunctionCall {
                name,
                args,
                signature,
            } => {
                let mapped_args =
                    allocator
                        .new_bump_vec_from_iter_result(args.iter().map(|arg| {
                            Self::map_expression(allocator, function_signatures, arg)
                        }))?;
                Expression::FunctionCall {
                    name: *name,
                    signature: Self::resolve_function_signature(function_signatures, name)?,
                    args: mapped_args,
                }
            }
        }))
    }

    fn resolve_function_signature(
        function_signatures: &FunctionSignaturesByName<'a, PhaseTopLevelDeclarationCollected<'a>>,
        name: &StringId,
    ) -> Result<
        &'a FunctionSignature<'a, PhaseTopLevelDeclarationCollected<'a>>,
        SemanticAnalysisError,
    > {
        function_signatures
            .get(name)
            .cloned()
            .ok_or(SemanticAnalysisError::FunctionNotFound {
                function_name: resolve_string_id(*name).expect("function name").to_owned(),
            })
    }
}

#[cfg(test)]
mod tests {
    use crate::phase_top_level_declaration_collector::TopLevelDeclarationCollector;
    use crate::semantic_analyzer::SemanticAnalysisError;
    use crate::Type;
    use parser::{
        get_or_create_string, AstAllocator, Expression, FunctionArgument, FunctionSignature,
        Statement,
    };

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
        let module = parser::parse(&ast_allocator, "test", SOURCE);

        let allocator = AstAllocator::default();
        let analyzed = TopLevelDeclarationCollector::analyze_module(&allocator, module)
            .expect("should have passed semantic analysis");

        assert_eq!(2, analyzed.function_signatures.len());
        assert_eq!(
            **analyzed
                .function_signatures
                .get(&get_or_create_string("main"))
                .expect("should find main"),
            FunctionSignature {
                name: get_or_create_string("main"),
                return_type: None,
                arguments: allocator.new_bump_vec(),
            }
        );
        let add_signature = analyzed
            .function_signatures
            .get(&get_or_create_string("add"))
            .expect("should find add");
        assert_eq!(
            **add_signature,
            FunctionSignature {
                name: get_or_create_string("add"),
                return_type: Some(Type::Int),
                arguments: allocator.new_bump_vec_from_iter(vec![
                    FunctionArgument {
                        name: get_or_create_string("a"),
                        arg_type: get_or_create_string("int"),
                    },
                    FunctionArgument {
                        name: get_or_create_string("b"),
                        arg_type: get_or_create_string("int"),
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
        let (name, args, signature) = match expression {
            Expression::FunctionCall {
                name,
                args,
                signature,
            } => (name, args, signature),
            _ => panic!("Expected a function call expression"),
        };
        assert_eq!(*name, get_or_create_string("add"));
        assert_eq!(signature, add_signature);
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

    #[test]
    fn function_call_not_found_resolved() {
        const SOURCE: &str = r"
fn main() {
    add(1, 2);
}
";

        let ast_allocator = parser::ParsedAstAllocator::default();
        let module = parser::parse(&ast_allocator, "test", SOURCE);

        let allocator = AstAllocator::default();
        let analyzed = TopLevelDeclarationCollector::analyze_module(&allocator, module)
            .expect_err("should not be valid");
        assert_eq!(
            analyzed,
            SemanticAnalysisError::FunctionNotFound {
                function_name: "add".to_string()
            }
        );
    }
}
