//! AST Walker for zokrates_pest_ast

use super::walkfns::*;
use super::CVisitorResult;

use lang_c::ast;
use lang_c::span::Node;

pub trait CVisitorMut<'ast>: Sized {
    fn visit_translation_unit(&mut self, tu: &mut ast::TranslationUnit) -> CVisitorResult {
        walk_translation_unit(self, tu)
    }

    fn visit_external_declaration(
        &mut self,
        external_decl: &mut Node<ast::ExternalDeclaration>,
    ) -> CVisitorResult {
        walk_external_declaration(self, &mut external_decl.node)
    }

    fn visit_declaration(&mut self, decl: &mut Node<ast::Declaration>) -> CVisitorResult {
        walk_declaration(self, &mut decl.node)
    }

    fn visit_storage_class(&mut self, sc: &mut Node<ast::StorageClassSpecifier>) -> CVisitorResult {
        walk_storage_class(self, &mut sc.node)
    }

    fn visit_type_specifier(&mut self, ts: &mut Node<ast::TypeSpecifier>) -> CVisitorResult {
        walk_type_specifier(self, &mut ts.node)
    }

    fn visit_type_qualifier(&mut self, tq: &mut Node<ast::TypeQualifier>) -> CVisitorResult {
        walk_type_qualifier(self, &mut tq.node)
    }

    fn visit_function_specifier(
        &mut self,
        fs: &mut Node<ast::FunctionSpecifier>,
    ) -> CVisitorResult {
        walk_function_specifier(self, &mut fs.node)
    }

    fn visit_declarator(&mut self, d: &mut Node<ast::Declarator>) -> CVisitorResult {
        walk_declarator(self, &mut d.node)
    }

    fn visit_initializer(&mut self, i: &mut Node<ast::Initializer>) -> CVisitorResult {
        walk_initializer(self, &mut i.node)
    }

    fn visit_static_assert(&mut self, _sa: &mut Node<ast::StaticAssert>) -> CVisitorResult {
        Ok(())
    }

    fn visit_function_definition(
        &mut self,
        _func_def: &mut Node<ast::FunctionDefinition>,
    ) -> CVisitorResult {
        Ok(())
    }

    fn visit_expression(&mut self, expr: &mut Node<ast::Expression>) -> CVisitorResult {
        walk_expression(self, &mut expr.node)
    }

    fn visit_identifier(&mut self, i: &mut Node<ast::Identifier>) -> CVisitorResult {
        walk_identifier(self, &mut i.node)
    }

    fn visit_constant(&mut self, c: &mut Node<ast::Constant>) -> CVisitorResult {
        walk_constant(self, &mut c.node)
    }

    fn visit_member_expression(&mut self, m: &mut Node<ast::MemberExpression>) -> CVisitorResult {
        walk_member_expression(self, &mut m.node)
    }

    fn visit_call_expression(&mut self, c: &mut Node<ast::CallExpression>) -> CVisitorResult {
        walk_call_expression(self, &mut c.node)
    }

    fn visit_unary_operator_expression(
        &mut self,
        u: &mut Box<Node<ast::UnaryOperatorExpression>>,
    ) -> CVisitorResult {
        walk_unary_operator_expression(self, &mut u.node)
    }

    fn visit_cast_expression(&mut self, c: &mut Node<ast::CastExpression>) -> CVisitorResult {
        walk_cast_expression(self, &mut c.node)
    }

    fn visit_binary_operator_expression(
        &mut self,
        b: &mut Box<Node<ast::BinaryOperatorExpression>>,
    ) -> CVisitorResult {
        walk_binary_operator_expression(self, &mut b.node)
    }

    fn visit_conditional_expression(
        &mut self,
        c: &mut Node<ast::ConditionalExpression>,
    ) -> CVisitorResult {
        walk_conditional_expression(self, &mut c.node)
    }

    fn visit_statement(&mut self, s: &mut Node<ast::Statement>) -> CVisitorResult {
        walk_statement(self, &mut s.node)
    }
}
