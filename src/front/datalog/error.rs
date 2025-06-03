//! Error implementation for datalog frontend

use thiserror::Error;

use super::parser::ast::Span;
use super::term::T;

use std::convert::From;
use std::fmt::{self, Display, Formatter};

#[derive(Error, Debug)]
/// An error in circuit translation
pub enum ErrorKind {
    #[error("Cannot apply operator '{0}' to '{1}'")]
    /// Cannot apply this operator to this term
    InvalidUnOp(String, T),
    #[error("Cannot apply operator '{0}' to\n\t{1}\nand\n\t{2}")]
    /// Cannot apply this operator to these terms
    InvalidBinOp(String, T, T),
    #[error("Could not find entry rule '{0}'")]
    /// Could not find the entry rule
    MissingEntry(String),
    #[error("Circify error: {0}")]
    /// Could not find the entry rule
    Circify(crate::circify::CircError),
}

#[derive(Debug)]
/// An error with an optional span
pub struct Error<'ast> {
    /// The error
    pub kind: Box<ErrorKind>,
    /// The span
    pub span: Option<Span<'ast>>,
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "Error: {}", self.kind)?;
        if let Some(s) = &self.span {
            writeln!(f, "\nLocation:")?;
            for l in s.lines() {
                writeln!(f, "  {l}")?;
            }
        }
        Ok(())
    }
}

impl From<ErrorKind> for Error<'_> {
    fn from(error_kind: ErrorKind) -> Self {
        Error {
            kind: Box::new(error_kind),
            span: None,
        }
    }
}

impl From<crate::circify::CircError> for Error<'_> {
    fn from(circ: crate::circify::CircError) -> Self {
        Error {
            kind: Box::new(ErrorKind::Circify(circ)),
            span: None,
        }
    }
}

impl<'ast> Error<'ast> {
    /// Attach span to error
    pub fn with_span(self, span: Span<'ast>) -> Self {
        Error {
            kind: self.kind,
            span: Some(span),
        }
    }
    /// New error, with span
    pub fn new(kind: ErrorKind, span: Span<'ast>) -> Self {
        Error {
            kind: Box::new(kind),
            span: Some(span),
        }
    }
}

/// Fallible value
pub type Result<'ast, T> = std::result::Result<T, Error<'ast>>;
