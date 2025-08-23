use crate::semantic_analyzer::SemanticAnalysisError;
use kigiri_memory::{StringId, resolve_string_id};
use parser::LiteralValue;
use std::fmt::Display;
use std::fmt::Formatter;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::Bool => write!(f, "bool"),
        }
    }
}

impl Type {
    pub fn to_string_short(&self) -> &'static str {
        match self {
            Type::I8 => "i8",
            Type::I16 => "i16",
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::U8 => "u8",
            Type::U16 => "u16",
            Type::U32 => "u32",
            Type::U64 => "u64",
            Type::F32 => "f32",
            Type::F64 => "f64",
            Type::Bool => "b",
        }
    }

    pub fn of_literal(literal: &LiteralValue) -> Self {
        match literal {
            LiteralValue::I8(_) => Type::I8,
            LiteralValue::I16(_) => Type::I16,
            LiteralValue::I32(_) => Type::I32,
            LiteralValue::I64(_) => Type::I64,
            LiteralValue::U8(_) => Type::U8,
            LiteralValue::U16(_) => Type::U16,
            LiteralValue::U32(_) => Type::U32,
            LiteralValue::U64(_) => Type::U64,
            LiteralValue::F32(_) => Type::F32,
            LiteralValue::F64(_) => Type::F64,
            LiteralValue::Boolean(_) => Type::Bool,
        }
    }

    pub fn name(t: Option<Type>) -> String {
        t.map_or("void".to_owned(), |t| t.to_string())
    }

    pub fn parse(type_name: StringId) -> Result<Type, SemanticAnalysisError> {
        let type_name =
            resolve_string_id(type_name).ok_or_else(|| SemanticAnalysisError::InternalError {
                message: "failed to resolve type name string id".to_string(),
            })?;
        match type_name {
            "i8" => Ok(Type::I8),
            "i16" => Ok(Type::I16),
            "i32" => Ok(Type::I32),
            "i64" => Ok(Type::I64),
            "u8" => Ok(Type::U8),
            "u16" => Ok(Type::U16),
            "u32" => Ok(Type::U32),
            "u64" => Ok(Type::U64),
            "f32" => Ok(Type::F32),
            "f64" => Ok(Type::F64),
            "bool" => Ok(Type::Bool),
            _ => Err(SemanticAnalysisError::TypeNotFound {
                type_name: type_name.to_string(),
            }),
        }
    }

    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
        )
    }

    pub fn is_unsigned(&self) -> bool {
        matches!(self, Type::U8 | Type::U16 | Type::U32 | Type::U64)
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Type::F32 | Type::F64)
    }

    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float()
    }
}
