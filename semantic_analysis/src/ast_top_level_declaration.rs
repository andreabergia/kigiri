use crate::Type;
use parser::{CompilationPhase, FunctionArgument, FunctionSignature, StringId};
use std::marker::PhantomData;

#[derive(Debug, PartialEq)]
pub struct PhaseTopLevelDeclarationCollected<'a> {
    phantom: PhantomData<&'a ()>,
}

impl<'a> CompilationPhase for PhaseTopLevelDeclarationCollected<'a> {
    type SymbolTableType = ();
    type FunctionArgumentType = FunctionArgument;
    type ExpressionType = ();
    type UnaryBinaryOperandType = ();
    type IdentifierType = StringId;
    type FunctionReturnType = Type;
    type FunctionCallSignatureType =
        &'a FunctionSignature<'a, PhaseTopLevelDeclarationCollected<'a>>;
}
