use std::fmt::Display;
use std::fmt::Formatter;

#[derive(Debug, PartialEq, Clone)]
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
    pub fn to_string_short(&self) -> String {
        match self {
            Type::Int => "i".to_string(),
            Type::Double => "d".to_string(),
            Type::Boolean => "b".to_string(),
        }
    }
}
