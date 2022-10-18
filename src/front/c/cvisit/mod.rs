//! AST Walker for lang_c_ast
#![allow(missing_docs)]

mod cvmut;
mod walkfns;

pub struct CVisitorError(pub String);
pub type CResult<T> = Result<T, CVisitorError>;
pub type CVisitorResult = CResult<()>;

pub use cvmut::CVisitorMut;

impl From<String> for CVisitorError {
    fn from(f: String) -> Self {
        Self(f)
    }
}
