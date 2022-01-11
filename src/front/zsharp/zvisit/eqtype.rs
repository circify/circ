//! AST Walker for zokrates_pest_ast

use super::{ZVisitorError, ZVisitorResult};

use zokrates_pest_ast as ast;

pub fn eq_type<'ast>(ty: &ast::Type<'ast>, ty2: &ast::Type<'ast>) -> ZVisitorResult {
    use ast::Type::*;
    match (ty, ty2) {
        (Basic(bty), Basic(bty2)) => eq_basic_type(bty, bty2),
        (Array(aty), Array(aty2)) => eq_array_type(aty, aty2),
        (Struct(sty), Struct(sty2)) => eq_struct_type(sty, sty2),
        _ => Err(ZVisitorError(format!(
            "type mismatch: expected {:?}, found {:?}",
            ty, ty2,
        ))),
    }
}

pub fn eq_basic_type<'ast>(
    ty: &ast::BasicType<'ast>,
    ty2: &ast::BasicType<'ast>,
) -> ZVisitorResult {
    use ast::BasicType::*;
    match (ty, ty2) {
        (Field(_), Field(_)) => Ok(()),
        (Boolean(_), Boolean(_)) => Ok(()),
        (U8(_), U8(_)) => Ok(()),
        (U16(_), U16(_)) => Ok(()),
        (U32(_), U32(_)) => Ok(()),
        (U64(_), U64(_)) => Ok(()),
        _ => Err(ZVisitorError(format!(
            "basic type mismatch: expected {:?}, found {:?}",
            ty, ty2,
        ))),
    }
}

pub fn eq_array_type<'ast>(
    ty: &ast::ArrayType<'ast>,
    ty2: &ast::ArrayType<'ast>,
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
        (Struct(sty), Struct(sty2)) => eq_struct_type(sty, sty2),
        _ => Err(ZVisitorError(format!(
            "array type mismatch: expected elms of type {:?}, found {:?}",
            &ty.ty, &ty2.ty,
        ))),
    }
}

pub fn eq_struct_type<'ast>(
    ty: &ast::StructType<'ast>,
    ty2: &ast::StructType<'ast>,
) -> ZVisitorResult {
    if ty.id.value != ty2.id.value {
        Err(ZVisitorError(format!(
            "struct type mismatch: expected {:?}, found {:?}",
            &ty.id.value, &ty2.id.value,
        )))
    } else {
        // don't check generics here; they'll get checked after monomorphization
        Ok(())
    }
}
