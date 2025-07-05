use crate::symbols::StringId;
use crate::{CompilationPhase, FunctionArgument, FunctionSignature};
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::marker::PhantomData;

#[derive(Debug, PartialEq)]
pub struct PhaseParsed<'a> {
    phantom: PhantomData<&'a ()>,
}

pub type FunctionSignaturesByName<'a> =
    HashMap<StringId, &'a FunctionSignature<'a, PhaseParsed<'a>>>;

impl<'a> CompilationPhase for PhaseParsed<'a> {
    type FunctionSignatureType = FunctionSignaturesByName<'a>;
    type SymbolTableType = ();
    type FunctionArgumentType = FunctionArgument;
    type ExpressionType = ();
    type UnaryBinaryOperandType = ();
    type IdentifierType = StringId;
    type FunctionReturnType = StringId;
    type FunctionSignatureData = ();
}
