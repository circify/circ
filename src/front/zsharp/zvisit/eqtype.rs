//! AST Walker for zokrates_pest_ast

use super::super::ZGen;
use super::{ZResult, ZVisitorError, ZVisitorResult};

use zokrates_pest_ast as ast;

pub(super) fn eq_type<'ast>(
    ty: &ast::Type<'ast>,
    ty2: &ast::Type<'ast>,
    zgen: &ZGen<'ast>,
) -> ZVisitorResult {
    use ast::Type::*;
    match (ty, ty2) {
        (Basic(bty), Basic(bty2)) => eq_basic_type(bty, bty2),
        (Array(aty), Array(aty2)) => eq_array_type(aty, aty2, zgen),
        (Struct(sty), Struct(sty2)) => eq_struct_type(sty, sty2, zgen),
        _ => Err(ZVisitorError(format!(
            "type mismatch: expected {ty:?}, found {ty2:?}"
        ))),
    }
}

fn eq_basic_type<'ast>(ty: &ast::BasicType<'ast>, ty2: &ast::BasicType<'ast>) -> ZVisitorResult {
    use ast::BasicType::*;
    match (ty, ty2) {
        (Field(_), Field(_)) => Ok(()),
        (Boolean(_), Boolean(_)) => Ok(()),
        (U8(_), U8(_)) => Ok(()),
        (U16(_), U16(_)) => Ok(()),
        (U32(_), U32(_)) => Ok(()),
        (U64(_), U64(_)) => Ok(()),
        _ => Err(ZVisitorError(format!(
            "basic type mismatch: expected {ty:?}, found {ty2:?}"
        ))),
    }
}

fn eq_array_type<'ast>(
    ty: &ast::ArrayType<'ast>,
    ty2: &ast::ArrayType<'ast>,
    zgen: &ZGen<'ast>,
) -> ZVisitorResult {
    use ast::BasicOrStructType::*;
    if ty.dimensions.len() != ty2.dimensions.len() {
        return Err(ZVisitorError(format!(
            "array type mismatch: expected {}-dimensional array, found {}-dimensional array",
            ty.dimensions.len(),
            ty2.dimensions.len(),
        )));
    }
    match (&ty.ty, &ty2.ty) {
        (Basic(bty), Basic(bty2)) => eq_basic_type(bty, bty2),
        (Struct(sty), Struct(sty2)) => eq_struct_type(sty, sty2, zgen),
        _ => Err(ZVisitorError(format!(
            "array type mismatch: expected elms of type {:?}, found {:?}",
            &ty.ty, &ty2.ty,
        ))),
    }
}

fn eq_struct_type<'ast>(
    ty: &ast::StructType<'ast>,
    ty2: &ast::StructType<'ast>,
    zgen: &ZGen<'ast>,
) -> ZVisitorResult {
    if ty.id.value == ty2.id.value {
        Ok(())
    } else if is_struct(&ty.id.value, zgen) && is_struct(&ty2.id.value, zgen) {
        // neither ty nor ty2 is a type alias, so they are really different
        Err(ZVisitorError(format!(
            "struct type mismatch: expected {:?}, found {:?}",
            &ty.id.value, &ty2.id.value,
        )))
    } else {
        eq_type(&canon_type(ty, zgen)?, &canon_type(ty2, zgen)?, zgen)
    }
}

fn is_struct(id: &str, zgen: &ZGen<'_>) -> bool {
    zgen.get_struct_or_type(id)
        .map(|(s, _)| s.is_ok())
        .unwrap_or(false)
}

fn canon_type<'ast>(ty: &ast::StructType<'ast>, zgen: &ZGen<'ast>) -> ZResult<ast::Type<'ast>> {
    zgen.get_struct_or_type(&ty.id.value)
        .map(|(s, _)| match s {
            Ok(sd) => ast::Type::Struct(ast::StructType {
                id: sd.id.clone(),
                explicit_generics: None,
                span: sd.span,
            }),
            Err(t) => t.ty.clone(),
        })
        .ok_or_else(|| {
            ZVisitorError(format!(
                "eqtype: unknown struct or type alias {}",
                &ty.id.value
            ))
        })
}
