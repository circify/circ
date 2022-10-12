//! AST Walker for lang_c_ast

use super::{CVisitorMut, CVisitorResult};
use lang_c::ast;

pub fn walk_translation_unit<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    tu: &mut ast::TranslationUnit,
) -> CVisitorResult {
    let ast::TranslationUnit(external_decls) = tu;
    external_decls
        .iter_mut()
        .try_for_each(|d| visitor.visit_external_declaration(d))?;
    Ok(())
}

pub fn walk_external_declaration<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    external_decl: &mut ast::ExternalDeclaration,
) -> CVisitorResult {
    use ast::ExternalDeclaration::*;
    match external_decl {
        Declaration(n) => visitor.visit_declaration(n),
        StaticAssert(n) => visitor.visit_static_assert(n),
        FunctionDefinition(n) => visitor.visit_function_definition(n),
    }
}

pub fn walk_declaration<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    decl: &mut ast::Declaration,
) -> CVisitorResult {
    use ast::DeclarationSpecifier::*;
    decl.specifiers
        .iter_mut()
        .try_for_each(|s| match &mut s.node {
            StorageClass(sc) => visitor.visit_storage_class(sc),
            TypeSpecifier(ts) => visitor.visit_type_specifier(ts),
            TypeQualifier(tq) => visitor.visit_type_qualifier(tq),
            Function(fs) => visitor.visit_function_specifier(fs),
            _ => todo!(),
        });

    decl.declarators.iter_mut().try_for_each(|d| {
        if let Some(i) = &mut d.node.initializer {
            visitor.visit_initializer(i);
        }
        visitor.visit_declarator(&mut d.node.declarator)
    });
    Ok(())
}

pub fn walk_storage_class<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    sc: &mut ast::StorageClassSpecifier,
) -> CVisitorResult {
    todo!()
}

pub fn walk_type_specifier<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    ts: &mut ast::TypeSpecifier,
) -> CVisitorResult {
    todo!()
}

pub fn walk_type_qualifier<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    tq: &mut ast::TypeQualifier,
) -> CVisitorResult {
    todo!()
}

pub fn walk_function_specifier<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    fs: &mut ast::FunctionSpecifier,
) -> CVisitorResult {
    todo!()
}

pub fn walk_declarator<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    fs: &mut ast::Declarator,
) -> CVisitorResult {
    todo!()
}

pub fn walk_initializer<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    fs: &mut ast::Initializer,
) -> CVisitorResult {
    todo!()
}

pub fn walk_expression<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    expr: &mut ast::Expression,
) -> CVisitorResult {
    use ast::Expression::*;
    match expr {
        Identifier(i) => visitor.visit_identifier(i),
        Constant(c) => todo!(),
        Member(m) => todo!(),
        Call(c) => todo!(),
        UnaryOperator(u) => todo!(),
        Cast(c) => todo!(),
        BinaryOperator(b) => todo!(),
        Conditional(c) => todo!(),
        Statement(s) => todo!(),
        _ => unimplemented!(),
    }
}

pub fn walk_identifier<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    expr: &mut ast::Identifier,
) -> CVisitorResult {
    todo!()
}
