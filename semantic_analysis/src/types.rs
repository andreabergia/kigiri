use crate::semantic_analyzer::SemanticAnalysisError;
use parser::{LiteralValue, StringId, resolve_string_id};
use std::fmt::Display;
use std::fmt::Formatter;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Type {
    Int,
    Double,
    Boolean,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Double => write!(f, "double"),
            Type::Boolean => write!(f, "boolean"),
        }
    }
}

impl Type {
    pub fn to_string_short(&self) -> &'static str {
        match self {
            Type::Int => "i",
            Type::Double => "d",
            Type::Boolean => "b",
        }
    }

    pub fn of_literal(literal: &LiteralValue) -> Self {
        match literal {
            LiteralValue::Integer(_) => Type::Int,
            LiteralValue::Double(_) => Type::Double,
            LiteralValue::Boolean(_) => Type::Boolean,
        }
    }

    pub fn name(t: Option<Type>) -> String {
        t.map_or("void".to_owned(), |t| t.to_string())
    }

    pub fn parse(type_name: StringId) -> Result<Type, SemanticAnalysisError> {
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
}
