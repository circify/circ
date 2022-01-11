//! AST Walker for zokrates_pest_ast
#![allow(missing_docs)]

mod eqtype;
mod walkfns;
mod zconstlitrw;
mod zgenericinf;
mod zstmtwalker;
mod zvmut;

pub(super) use zconstlitrw::ZConstLiteralRewriter;
pub(super) use zgenericinf::ZGenericInf;
pub(super) use zstmtwalker::ZStatementWalker;
pub use zvmut::ZVisitorMut;

use zokrates_pest_ast as ast;

pub struct ZVisitorError(pub String);
pub type ZResult<T> = Result<T, ZVisitorError>;
pub type ZVisitorResult = ZResult<()>;

impl From<String> for ZVisitorError {
    fn from(f: String) -> Self {
        Self(f)
    }
}

fn bos_to_type(bos: ast::BasicOrStructType) -> ast::Type {
    use ast::{BasicOrStructType::*, Type};
    match bos {
        Struct(st) => Type::Struct(st),
        Basic(bt) => Type::Basic(bt),
    }
}
