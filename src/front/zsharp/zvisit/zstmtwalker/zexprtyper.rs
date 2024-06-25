//! AST Walker for zokrates_pest_ast

use super::super::eqtype::*;
use super::super::{bos_to_type, ZResult, ZVisitorError, ZVisitorMut, ZVisitorResult};
use super::ZStatementWalker;

use zokrates_pest_ast as ast;

pub(super) struct ZExpressionTyper<'ast, 'ret, 'wlk> {
    walker: &'wlk ZStatementWalker<'ast, 'ret>,
    ty: Option<ast::Type<'ast>>,
}

impl<'ast, 'ret, 'wlk> ZExpressionTyper<'ast, 'ret, 'wlk> {
    pub fn new(walker: &'wlk ZStatementWalker<'ast, 'ret>) -> Self {
        Self { walker, ty: None }
    }

    pub fn take(&mut self) -> ZResult<Option<ast::Type<'ast>>> {
        self.ty
            .take()
            .map(|t| self.walker.canon_type(t))
            .transpose()
    }

    fn visit_identifier_expression_t(
        &mut self,
        ie: &ast::IdentifierExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        self.walker.lookup_type(ie).map(|t| {
            self.ty.replace(t);
        })
    }

    fn arrayize(
        &self,
        ty: ast::Type<'ast>,
        cnt: ast::Expression<'ast>,
        spn: &ast::Span<'ast>,
    ) -> ast::ArrayType<'ast> {
        use ast::Type::*;
        match ty {
            Array(mut aty) => {
                aty.dimensions.insert(0, cnt);
                aty
            }
            Basic(bty) => ast::ArrayType {
                ty: ast::BasicOrStructType::Basic(bty),
                dimensions: vec![cnt],
                span: *spn,
            },
            Struct(sty) => ast::ArrayType {
                ty: ast::BasicOrStructType::Struct(sty),
                dimensions: vec![cnt],
                span: *spn,
            },
        }
    }
}

impl<'ast, 'ret, 'wlk> ZVisitorMut<'ast> for ZExpressionTyper<'ast, 'ret, 'wlk> {
    fn visit_expression(&mut self, expr: &mut ast::Expression<'ast>) -> ZVisitorResult {
        use ast::Expression::*;
        if self.ty.is_some() {
            return Err(ZVisitorError(
                "ZExpressionTyper: type found at expression entry?".to_string(),
            ));
        }
        match expr {
            Ternary(te) => self.visit_ternary_expression(te),
            Binary(be) => self.visit_binary_expression(be),
            Unary(ue) => self.visit_unary_expression(ue),
            Postfix(pe) => self.visit_postfix_expression(pe),
            Identifier(ie) => self.visit_identifier_expression_t(ie),
            Literal(le) => self.visit_literal_expression(le),
            InlineArray(iae) => self.visit_inline_array_expression(iae),
            InlineStruct(ise) => self.visit_inline_struct_expression(ise),
            ArrayInitializer(aie) => self.visit_array_initializer_expression(aie),
        }
    }

    fn visit_ternary_expression(
        &mut self,
        te: &mut ast::TernaryExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        self.visit_expression(&mut te.second)?;
        let ty2 = self.take()?;
        self.visit_expression(&mut te.third)?;
        let ty3 = self.take()?;
        match (ty2, ty3) {
            (Some(t), None) => self.ty.replace(t),
            (None, Some(t)) => self.ty.replace(t),
            (Some(t1), Some(t2)) => {
                eq_type(&t1, &t2, self.walker.zgen)?;
                self.ty.replace(t2)
            }
            (None, None) => None,
        };
        Ok(())
    }

    fn visit_binary_expression(&mut self, be: &mut ast::BinaryExpression<'ast>) -> ZVisitorResult {
        use ast::{BasicType::*, BinaryOperator::*, Type::*};
        assert!(self.ty.is_none());
        match &be.op {
            Or | And | Eq | NotEq | Lt | Gt | Lte | Gte => {
                self.ty
                    .replace(Basic(Boolean(ast::BooleanType { span: be.span })));
            }
            Pow => {
                self.ty
                    .replace(Basic(Field(ast::FieldType { span: be.span })));
            }
            BitXor | BitAnd | BitOr | RightShift | LeftShift | Add | Sub | Mul | Div | Rem => {
                self.visit_expression(&mut be.left)?;
                let ty_l = self.take()?;
                self.visit_expression(&mut be.right)?;
                let ty_r = self.take()?;
                if let Some(ty) = match (ty_l, ty_r) {
                    (Some(t), None) => Some(t),
                    (None, Some(t)) => Some(t),
                    (Some(t1), Some(t2)) => {
                        eq_type(&t1, &t2, self.walker.zgen)?;
                        Some(t2)
                    }
                    (None, None) => None,
                } {
                    if !matches!(&ty, Basic(_)) {
                        return Err(ZVisitorError(
                            "ZExpressionTyper: got non-Basic type for a binop".to_string(),
                        ));
                    }
                    if matches!(&ty, Basic(Boolean(_))) {
                        return Err(ZVisitorError(
                            "ZExpressionTyper: got Bool for a binop that cannot support it"
                                .to_string(),
                        ));
                    }
                    if matches!(&be.op, BitXor | BitAnd | BitOr | RightShift | LeftShift)
                        && matches!(&ty, Basic(Field(_)))
                    {
                        return Err(ZVisitorError(
                            "ZExpressionTyper: got Field for a binop that cannot support it"
                                .to_string(),
                        ));
                    }
                    self.ty.replace(ty);
                }
            }
        };
        Ok(())
    }

    fn visit_unary_expression(&mut self, ue: &mut ast::UnaryExpression<'ast>) -> ZVisitorResult {
        use ast::{BasicType::*, Type::*, UnaryOperator::*};
        assert!(self.ty.is_none());
        self.visit_expression(&mut ue.expression)?;
        self.ty = self.take()?; // canonicalize
        match &ue.op {
            Pos(_) | Neg(_) => {
                if let Some(ty) = &self.ty {
                    if !matches!(ty, Basic(_)) || matches!(ty, Basic(Boolean(_))) {
                        return Err(ZVisitorError(
                            "ZExpressionTyper: got Bool or non-Basic for unary op".to_string(),
                        ));
                    }
                }
            }
            Not(_) => {
                if let Some(ty) = &self.ty {
                    if !matches!(ty, Basic(_)) || matches!(ty, Basic(Field(_))) {
                        return Err(ZVisitorError(
                            "ZExpressionTyper: got Field or non-Basic for unary !".to_string(),
                        ));
                    }
                }
            }
            Strict(_) => (),
        }
        Ok(())
    }

    fn visit_boolean_literal_expression(
        &mut self,
        ble: &mut ast::BooleanLiteralExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        self.ty.replace(ast::Type::Basic(ast::BasicType::Boolean(
            ast::BooleanType { span: ble.span },
        )));
        Ok(())
    }

    fn visit_decimal_suffix(&mut self, ds: &mut ast::DecimalSuffix<'ast>) -> ZVisitorResult {
        assert!(self.ty.is_none());
        use ast::{BasicType::*, DecimalSuffix as DS, Type::*};
        match ds {
            DS::U8(s) => self.ty.replace(Basic(U8(ast::U8Type { span: s.span }))),
            DS::U16(s) => self.ty.replace(Basic(U16(ast::U16Type { span: s.span }))),
            DS::U32(s) => self.ty.replace(Basic(U32(ast::U32Type { span: s.span }))),
            DS::U64(s) => self.ty.replace(Basic(U64(ast::U64Type { span: s.span }))),
            DS::Field(s) => self
                .ty
                .replace(Basic(Field(ast::FieldType { span: s.span }))),
        };
        Ok(())
    }

    fn visit_hex_number_expression(
        &mut self,
        hne: &mut ast::HexNumberExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        use ast::{BasicType::*, HexNumberExpression as HNE, Type::*};
        match hne {
            HNE::U8(s) => self.ty.replace(Basic(U8(ast::U8Type { span: s.span }))),
            HNE::U16(s) => self.ty.replace(Basic(U16(ast::U16Type { span: s.span }))),
            HNE::U32(s) => self.ty.replace(Basic(U32(ast::U32Type { span: s.span }))),
            HNE::U64(s) => self.ty.replace(Basic(U64(ast::U64Type { span: s.span }))),
        };
        Ok(())
    }

    fn visit_array_initializer_expression(
        &mut self,
        aie: &mut ast::ArrayInitializerExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        use ast::Type::*;

        self.visit_expression(&mut aie.value)?;
        if let Some(ty) = self.take()? {
            let ty = self.arrayize(ty, aie.count.as_ref().clone(), &aie.span);
            self.ty.replace(Array(ty));
        }
        Ok(())
    }

    fn visit_inline_struct_expression(
        &mut self,
        ise: &mut ast::InlineStructExpression<'ast>,
    ) -> ZVisitorResult {
        // XXX(unimpl) we don't monomorphize struct type here... OK?
        self.visit_identifier_expression_t(&ise.ty)
    }

    fn visit_inline_array_expression(
        &mut self,
        iae: &mut ast::InlineArrayExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        assert!(!iae.expressions.is_empty());

        let mut acc_ty = None;
        let mut acc_len = 0;
        iae.expressions
            .iter_mut()
            .try_for_each::<_, ZVisitorResult>(|soe| {
                self.visit_spread_or_expression(soe)?;
                if let Some(ty) = self.take()? {
                    let (nty, nln) = if matches!(soe, ast::SpreadOrExpression::Expression(_)) {
                        Ok((ty, 1))
                    } else if let ast::Type::Array(mut at) = ty {
                        assert!(!at.dimensions.is_empty());
                        let len = self.walker.zgen.const_usize_(&at.dimensions[0])?;
                        if at.dimensions.len() == 1 {
                            Ok((bos_to_type(at.ty), len))
                        } else {
                            at.dimensions.remove(0);
                            Ok((ast::Type::Array(at), len))
                        }
                    } else {
                        Err(format!(
                            "ZExpressionTyper: Spread expression: expected array, got {ty:?}"
                        ))
                    }?;

                    if let Some(acc) = &acc_ty {
                        eq_type(acc, &nty, self.walker.zgen)?;
                    } else {
                        acc_ty.replace(nty);
                    }
                    acc_len += nln;
                    Ok(())
                } else if matches!(soe, ast::SpreadOrExpression::Expression(_)) {
                    // assume expression type is OK, just increment count
                    acc_len += 1;
                    Ok(())
                } else {
                    Err(ZVisitorError(format!(
                        "ZExpressionTyper: Could not type SpreadOrExpression::Spread {soe:#?}",
                    )))
                }
            })?;

        self.ty = acc_ty.map(|at| {
            ast::Type::Array(self.arrayize(
                at,
                ast::Expression::Literal(ast::LiteralExpression::HexLiteral(
                    ast::HexLiteralExpression {
                        value: ast::HexNumberExpression::U32(ast::U32NumberExpression {
                            value: format!("{acc_len:04x}"),
                            span: iae.span,
                        }),
                        span: iae.span,
                    },
                )),
                &iae.span,
            ))
        });
        Ok(())
    }

    fn visit_postfix_expression(
        &mut self,
        pfe: &mut ast::PostfixExpression<'ast>,
    ) -> ZVisitorResult {
        assert!(self.ty.is_none());
        self.ty.replace(self.walker.get_postfix_ty(pfe, None)?);
        Ok(())
    }
}
