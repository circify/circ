//! AST Walker for zokrates_pest_ast
#![allow(missing_docs)]

mod eqtype;
mod walkfns;
mod zconstlitrw;
mod zgenericinf;
mod zstmtwalker;
mod zvmut;

pub use zvmut::ZVisitorMut;
pub(super) use zconstlitrw::ZConstLiteralRewriter;
pub(super) use zgenericinf::ZGenericInf;
pub(super) use zstmtwalker::ZStatementWalker;

use zokrates_pest_ast as ast;

pub struct ZVisitorError(pub String);
pub type ZResult<T> = Result<T, ZVisitorError>;
pub type ZVisitorResult = ZResult<()>;

impl From<String> for ZVisitorError {
    fn from(f: String) -> Self {
        Self(f)
    }
}

fn bos_to_type<'ast>(bos: ast::BasicOrStructType<'ast>) -> ast::Type<'ast> {
    use ast::{BasicOrStructType::*, Type};
    match bos {
        Struct(st) => Type::Struct(st),
        Basic(bt) => Type::Basic(bt),
    }
}
