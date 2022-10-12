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
            _ => unimplemented!("CAstWalker unimplemented specifier: {:?}", s),
        })?;

    decl.declarators.iter_mut().try_for_each(|d| {
        if let Some(i) = &mut d.node.initializer {
            visitor.visit_initializer(i)?;
        }
        visitor.visit_declarator(&mut d.node.declarator)
    })?;
    Ok(())
}

pub fn walk_storage_class<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _sc: &mut ast::StorageClassSpecifier,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_type_specifier<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _ts: &mut ast::TypeSpecifier,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_type_qualifier<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _tq: &mut ast::TypeQualifier,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_function_specifier<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _fs: &mut ast::FunctionSpecifier,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_declarator<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _fs: &mut ast::Declarator,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_initializer<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _fs: &mut ast::Initializer,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_expression<'ast, C: CVisitorMut<'ast>>(
    visitor: &mut C,
    expr: &mut ast::Expression,
) -> CVisitorResult {
    use ast::Expression::*;
    match expr {
        Identifier(i) => visitor.visit_identifier(i),
        Constant(c) => visitor.visit_constant(c),
        Member(m) => visitor.visit_member_expression(m),
        Call(c) => visitor.visit_call_expression(c),
        UnaryOperator(u) => visitor.visit_unary_operator_expression(u),
        Cast(c) => visitor.visit_cast_expression(c),
        BinaryOperator(b) => visitor.visit_binary_operator_expression(b),
        Conditional(c) => visitor.visit_conditional_expression(c),
        Statement(s) => visitor.visit_statement(s),
        _ => unimplemented!("CAstWalker unimplemented expression: {:?}", expr),
    }
}

pub fn walk_identifier<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::Identifier,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_constant<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::Constant,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_member_expression<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::MemberExpression,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_call_expression<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::CallExpression,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_unary_operator_expression<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::UnaryOperatorExpression,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_cast_expression<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::CastExpression,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_binary_operator_expression<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::BinaryOperatorExpression,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_conditional_expression<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::ConditionalExpression,
) -> CVisitorResult {
    Ok(())
}

pub fn walk_statement<'ast, C: CVisitorMut<'ast>>(
    _visitor: &mut C,
    _expr: &mut ast::Statement,
) -> CVisitorResult {
    Ok(())
}
