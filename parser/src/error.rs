use crate::grammar::Rule;
use pest::error::Error as PestError;
use std::num::{ParseFloatError, ParseIntError};
use std::str::ParseBoolError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Syntax error: {0}")]
    SyntaxError(#[from] Box<PestError<Rule>>),

    #[error("Failed to parse integer: {text}")]
    IntegerParseError {
        text: String,
        #[source]
        source: ParseIntError,
    },

    #[error("Failed to parse float: {text}")]
    FloatParseError {
        text: String,
        #[source]
        source: ParseFloatError,
    },

    #[error("Failed to parse boolean: {text}")]
    BooleanParseError {
        text: String,
        #[source]
        source: ParseBoolError,
    },

    #[error("Internal parser error: {message}")]
    InternalError { message: String },
}

pub type ParseResult<T> = Result<T, ParseError>;
