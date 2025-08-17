use crate::PhaseTypeResolved;
use crate::semantic_analyzer::SemanticAnalysisError;
use kigiri_memory::resolve_string_id;
use parser::{Block, FunctionDeclaration, IfElseBlock, Module, Statement};

pub(crate) struct ReturnPathAnalyzer {}

impl ReturnPathAnalyzer {
    pub(crate) fn analyze_module(
        module: &Module<PhaseTypeResolved>,
    ) -> Result<(), SemanticAnalysisError> {
        for function in &module.functions {
            Self::check_function(function)?;
        }
        Ok(())
    }

    fn check_function(
        function: &FunctionDeclaration<PhaseTypeResolved>,
    ) -> Result<(), SemanticAnalysisError> {
        // Functions that return nothing are fine, the implicit return is added
        if function.signature.return_type.is_none() {
            return Ok(());
        }

        if !Self::block_returns(function.body) {
            let function_name = resolve_string_id(function.signature.name)
                .ok_or_else(|| SemanticAnalysisError::InternalError {
                    message: "failed to resolve function name".to_string(),
                })?
                .to_string();
            Err(SemanticAnalysisError::NotAllPathsReturnAValue { function_name })
        } else {
            Ok(())
        }
    }

    fn block_returns(block: &Block<PhaseTypeResolved>) -> bool {
        // A block returns if its last statement returns.
        block
            .statements
            .last()
            .is_some_and(|s| Self::statement_returns(s))
    }

    fn statement_returns(statement: &Statement<PhaseTypeResolved>) -> bool {
        match statement {
            Statement::Return { .. } => true,
            Statement::If(if_statement) => {
                if let Some(else_block) = if_statement.else_block {
                    Self::block_returns(if_statement.then_block)
                        && Self::if_else_block_returns(else_block)
                } else {
                    false // if without else
                }
            }
            Statement::NestedBlock { block } => Self::block_returns(block),
            Statement::Loop { body } => !Self::block_contains_break(body),
            Statement::While { .. } => false,
            _ => false,
        }
    }

    fn if_else_block_returns(else_block: &IfElseBlock<PhaseTypeResolved>) -> bool {
        match else_block {
            IfElseBlock::Block(b) => Self::block_returns(b),
            IfElseBlock::If(s) => Self::statement_returns(&Statement::If(s)),
        }
    }

    fn block_contains_break(block: &Block<PhaseTypeResolved>) -> bool {
        block
            .statements
            .iter()
            .any(|s| Self::statement_contains_break(s))
    }

    fn statement_contains_break(statement: &Statement<PhaseTypeResolved>) -> bool {
        match statement {
            Statement::Break => true,
            Statement::If(if_statement) => {
                Self::block_contains_break(if_statement.then_block)
                    || if_statement
                        .else_block
                        .is_some_and(Self::if_else_block_contains_break)
            }
            Statement::NestedBlock { block } => Self::block_contains_break(block),
            // A loop statement itself doesn't "contain" a break in a way that affects an outer loop.
            // It "swallows" the breaks. So we don't recurse into inner loops.
            Statement::While { .. } => false,
            Statement::Loop { .. } => false,
            _ => false,
        }
    }

    fn if_else_block_contains_break(else_block: &IfElseBlock<PhaseTypeResolved>) -> bool {
        match else_block {
            IfElseBlock::Block(b) => Self::block_contains_break(b),
            IfElseBlock::If(s) => Self::statement_contains_break(&Statement::If(s)),
        }
    }
}
