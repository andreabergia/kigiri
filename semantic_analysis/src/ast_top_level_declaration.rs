use parser::{CompilationPhase, FunctionArgument, StringId};
use std::marker::PhantomData;

#[derive(Debug, PartialEq)]
pub struct PhaseTopLevelDeclarationCollected<'a> {
    phantom: PhantomData<&'a ()>,
}

impl CompilationPhase for PhaseTopLevelDeclarationCollected<'_> {
    type SymbolTableType = ();
    type FunctionArgumentType = FunctionArgument;
    type ExpressionType = ();
    type UnaryBinaryOperandType = ();
    type IdentifierType = StringId;
    type FunctionReturnType = StringId;
    type FunctionCallReturnType = ();
}
