use thiserror::Error;

#[derive(Error, Debug, PartialEq)]
pub enum CodegenError {
    #[error("Internal codegen error: {message}")]
    InternalError { message: String },
}

pub type CodegenResult<T> = Result<T, CodegenError>;
