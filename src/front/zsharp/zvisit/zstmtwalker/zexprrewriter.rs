//! AST Walker for zokrates_pest_ast

use super::{ZVisitorMut, ZVisitorResult};

use std::collections::HashMap;
use zokrates_pest_ast as ast;

pub(super) struct ZExpressionRewriter<'ast> {
    gvmap: HashMap<String, ast::Expression<'ast>>,
}

impl<'ast> ZExpressionRewriter<'ast> {
    pub fn new(gvmap: HashMap<String, ast::Expression<'ast>>) -> Self {
        Self { gvmap }
    }
}

impl<'ast> ZVisitorMut<'ast> for ZExpressionRewriter<'ast> {
    fn visit_expression(&mut self, expr: &mut ast::Expression<'ast>) -> ZVisitorResult {
        use ast::Expression::*;
        match expr {
            Ternary(te) => self.visit_ternary_expression(te),
            Binary(be) => self.visit_binary_expression(be),
            Unary(ue) => self.visit_unary_expression(ue),
            Postfix(pe) => self.visit_postfix_expression(pe),
            Literal(le) => self.visit_literal_expression(le),
            InlineArray(iae) => self.visit_inline_array_expression(iae),
            InlineStruct(ise) => self.visit_inline_struct_expression(ise),
            ArrayInitializer(aie) => self.visit_array_initializer_expression(aie),
            Identifier(ie) => {
                if let Some(e) = self.gvmap.get(&ie.value) {
                    *expr = e.clone();
                    Ok(())
                } else {
                    self.visit_identifier_expression(ie)
                }
            }
        }
    }
}
