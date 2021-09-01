//! AST Walker for zokrates_pest_ast
#![allow(missing_docs)]

mod walkfns;
mod zconstlitrw;
mod zstmtwalker;
mod zvmut;

pub use zvmut::ZVisitorMut;
pub(super) use zconstlitrw::ZConstLiteralRewriter;
pub(super) use zstmtwalker::ZStatementWalker;

pub struct ZVisitorError(pub String);
pub type ZResult<T> = Result<T, ZVisitorError>;
pub type ZVisitorResult = ZResult<()>;

impl From<String> for ZVisitorError {
    fn from(f: String) -> Self {
        Self(f)
    }
}
