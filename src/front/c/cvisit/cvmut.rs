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

    fn visit_static_assert(&mut self, sa: &mut Node<ast::StaticAssert>) -> CVisitorResult {
        todo!()
    }

    fn visit_function_definition(
        &mut self,
        func_def: &mut Node<ast::FunctionDefinition>,
    ) -> CVisitorResult {
        todo!()
        // walk_external_declaration(self, external_decl)
    }

    fn visit_expression(&mut self, expr: &mut Node<ast::Expression>) -> CVisitorResult {
        walk_expression(self, &mut expr.node)
    }

    fn visit_identifier(&mut self, i: &mut Node<ast::Identifier>) -> CVisitorResult {
        walk_identifier(self, &mut i.node)
    }
}
