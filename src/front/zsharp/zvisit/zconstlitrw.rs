//! AST Walker for zokrates_pest_ast

use super::super::term::Ty;
use super::walkfns::*;
use super::{ZVisitorError, ZVisitorMut, ZVisitorResult};

use zokrates_pest_ast as ast;

pub(in super::super) struct ZConstLiteralRewriter {
    to_ty: Option<Ty>,
    found: bool,
}

impl ZConstLiteralRewriter {
    pub fn new(to_ty: Option<Ty>) -> Self {
        Self {
            to_ty,
            found: false,
        }
    }

    #[allow(dead_code)]
    pub fn found(&self) -> bool {
        self.found
    }

    pub fn replace(&mut self, to_ty: Option<Ty>) -> Option<Ty> {
        std::mem::replace(&mut self.to_ty, to_ty)
    }
}

impl<'ast> ZVisitorMut<'ast> for ZConstLiteralRewriter {
    /*
    Expressions can be any of:

    Binary(BinaryExpression<'ast>),
        -> depends on operator. e.g., == outputs Bool but takes in arbitrary l and r

    Ternary(TernaryExpression<'ast>)
        -> first expr is Bool, other two are expected type

    Unary(UnaryExpression<'ast>),
        -> no change to expected type: each sub-expr should have the expected type

    Postfix(PostfixExpression<'ast>),
        -> cannot type Access results, but descend into sub-exprs to type array indices

    Identifier(IdentifierExpression<'ast>),
        -> nothing to do (terminal)

    Literal(LiteralExpression<'ast>),
        -> literal should have same type as expression

    InlineArray(InlineArrayExpression<'ast>),
        -> descend into SpreadOrExpression, looking for either array or element type

    InlineStruct(InlineStructExpression<'ast>),
        -> check that struct types are equal

    ArrayInitializer(ArrayInitializerExpression<'ast>),
        -> value should have type of value inside Array
        -> count should have type Field
    */

    fn visit_ternary_expression(
        &mut self,
        te: &mut ast::TernaryExpression<'ast>,
    ) -> ZVisitorResult {
        // first expression in a ternary should have type bool
        let to_ty = self.replace(Some(Ty::Bool));
        self.visit_expression(&mut te.first)?;
        self.replace(to_ty);
        self.visit_expression(&mut te.second)?;
        self.visit_expression(&mut te.third)?;
        self.visit_span(&mut te.span)
    }

    fn visit_binary_expression(&mut self, be: &mut ast::BinaryExpression<'ast>) -> ZVisitorResult {
        let (ty_l, ty_r) = {
            use ast::BinaryOperator::*;
            match be.op {
                Pow | RightShift | LeftShift => (self.to_ty.clone(), Some(Ty::Uint(32))),
                Eq | NotEq | Lt | Gt | Lte | Gte => (None, None),
                _ => (self.to_ty.clone(), self.to_ty.clone()),
            }
        };
        self.visit_binary_operator(&mut be.op)?;
        let to_ty = self.replace(ty_l);
        self.visit_expression(&mut be.left)?;
        self.replace(ty_r);
        self.visit_expression(&mut be.right)?;
        self.replace(to_ty);
        self.visit_span(&mut be.span)
    }

    fn visit_decimal_literal_expression(
        &mut self,
        dle: &mut ast::DecimalLiteralExpression<'ast>,
    ) -> ZVisitorResult {
        if dle.suffix.is_none() && self.to_ty.is_some() {
            self.found = true;
            dle.suffix.replace(match self.to_ty.as_ref().unwrap() {
                Ty::Uint(8) => Ok(ast::DecimalSuffix::U8(ast::U8Suffix {
                    span: dle.span,
                })),
                Ty::Uint(16) => Ok(ast::DecimalSuffix::U16(ast::U16Suffix {
                    span: dle.span,
                })),
                Ty::Uint(32) => Ok(ast::DecimalSuffix::U32(ast::U32Suffix {
                    span: dle.span,
                })),
                Ty::Uint(64) => Ok(ast::DecimalSuffix::U64(ast::U64Suffix {
                    span: dle.span,
                })),
                Ty::Uint(_) => Err(
                    "ZConstLiteralRewriter: Uint size must be divisible by 8".to_string(),
                ),
                Ty::Field => Ok(ast::DecimalSuffix::Field(ast::FieldSuffix {
                    span: dle.span,
                })),
                _ => Err(
                    "ZConstLiteralRewriter: rewriting DecimalLiteralExpression to incompatible type"
                        .to_string(),
                ),
            }?);
        }
        walk_decimal_literal_expression(self, dle)
    }

    fn visit_array_initializer_expression(
        &mut self,
        aie: &mut ast::ArrayInitializerExpression<'ast>,
    ) -> ZVisitorResult {
        if self.to_ty.is_some() {
            if let Ty::Array(_, arr_ty) = self.to_ty.clone().unwrap() {
                // ArrayInitializerExpression::value should match arr_ty
                let to_ty = self.replace(Some(*arr_ty));
                self.visit_expression(&mut aie.value)?;
                self.to_ty = to_ty;
            } else {
                return Err(
                    "ZConstLiteralRewriter: rewriting ArrayInitializerExpression to non-Array type"
                        .to_string()
                        .into(),
                );
            }
        }

        // always rewrite ArrayInitializerExpression::count literals to type U32
        let to_ty = self.replace(Some(Ty::Uint(32)));
        self.visit_expression(&mut aie.count)?;
        self.to_ty = to_ty;

        self.visit_span(&mut aie.span)
    }

    fn visit_inline_struct_expression(
        &mut self,
        ise: &mut ast::InlineStructExpression<'ast>,
    ) -> ZVisitorResult {
        self.visit_identifier_expression(&mut ise.ty)?;

        let to_ty = self.replace(None);
        let ty_map = if let Some(t) = to_ty.as_ref() {
            if let Ty::Struct(name, ty_map) = t {
                if name != &ise.ty.value {
                    Err(format!("ZConstLiteralRewriter: got struct {}, expected {} visiting inline struct expression", &ise.ty.value, name))
                } else {
                    Ok(Some(ty_map.clone()))
                }
            } else {
                Err(
                    "ZConstLiteralRewriter: rewriting InlineStructExpression to non-Struct type"
                        .to_string(),
                )
            }
        } else {
            Ok(None)
        }?;

        if let Some(ty_map) = ty_map {
            let mut ty_map = ty_map.into_map();
            let (mem, str_name) = (&mut ise.members, &ise.ty.value);
            mem.iter_mut()
                .try_for_each(|m| ty_map
                    .remove(&m.id.value)
                    .ok_or_else(|| ZVisitorError(format!(
                        "ZConstLiteralRewriter: no member {} in struct {}, or duplicate member in inline expression",
                        &m.id.value,
                        str_name,
                    )))
                    .and_then(|ty| {
                        self.to_ty = Some(ty);
                        self.visit_inline_struct_member(m)
                    })
                )?;

            if !ty_map.is_empty() {
                return Err(format!(
                    "ZConstLiteralRewriter: inline expression for struct {} has extra fields: {:?}",
                    &ise.ty.value,
                    ty_map.keys().collect::<Vec<_>>(),
                )
                .into());
            }
        } else {
            ise.members
                .iter_mut()
                .try_for_each(|m| self.visit_inline_struct_member(m))?;
        }
        self.to_ty = to_ty;

        self.visit_span(&mut ise.span)
    }

    fn visit_inline_array_expression(
        &mut self,
        iae: &mut ast::InlineArrayExpression<'ast>,
    ) -> ZVisitorResult {
        let mut inner_ty = if let Some(t) = self.to_ty.as_ref() {
            if let Ty::Array(_, arr_ty) = t.clone() {
                Ok(Some(*arr_ty))
            } else {
                Err(
                    "ZConstLiteralRewriter: rewriting InlineArrayExpression to non-Array type"
                        .to_string(),
                )
            }
        } else {
            Ok(None)
        }?;

        for e in iae.expressions.iter_mut() {
            use ast::SpreadOrExpression::*;
            match e {
                Spread(s) => {
                    // a spread expression is an array; array type should match (we ignore number)
                    self.visit_spread(s)?;
                }
                Expression(e) => {
                    // an expression here is an individual array element, inner type should match
                    inner_ty = self.replace(inner_ty);
                    self.visit_expression(e)?;
                    inner_ty = self.replace(inner_ty);
                }
            }
        }

        self.visit_span(&mut iae.span)
    }

    fn visit_postfix_expression(
        &mut self,
        pe: &mut ast::PostfixExpression<'ast>,
    ) -> ZVisitorResult {
        self.visit_identifier_expression(&mut pe.id)?;

        // descend into accesses. we do not know expected type for these expressions
        // (but we may end up descending into an ArrayAccess, which would get typed)
        let to_ty = self.replace(None);
        pe.accesses
            .iter_mut()
            .try_for_each(|a| self.visit_access(a))?;
        self.to_ty = to_ty;

        self.visit_span(&mut pe.span)
    }

    fn visit_array_type(&mut self, aty: &mut ast::ArrayType<'ast>) -> ZVisitorResult {
        // ArrayType.ty should match arr_ty
        let to_ty = self.replace(
            self.to_ty
                .as_ref()
                .map(|to_ty| {
                    if let Ty::Array(_, arr_ty) = to_ty {
                        Ok(*arr_ty.clone())
                    } else {
                        Err(
                            "ZConstLiteralRewriter: rewriting ArrayType to non-Array type"
                                .to_string(),
                        )
                    }
                })
                .transpose()?,
        );
        self.visit_basic_or_struct_type(&mut aty.ty)?;

        // always rewrite ArrayType::dimensions literals to type U32
        self.replace(Some(Ty::Uint(32)));
        aty.dimensions
            .iter_mut()
            .try_for_each(|d| self.visit_expression(d))?;
        self.to_ty = to_ty;

        self.visit_span(&mut aty.span)
    }

    fn visit_explicit_generics(&mut self, eg: &mut ast::ExplicitGenerics<'ast>) -> ZVisitorResult {
        // always rewrite ConstantGenericValue literals to type U32
        let to_ty = self.replace(Some(Ty::Uint(32)));
        walk_explicit_generics(self, eg)?;
        self.to_ty = to_ty;
        Ok(())
    }

    fn visit_field_type(&mut self, fty: &mut ast::FieldType<'ast>) -> ZVisitorResult {
        if self.to_ty.is_some() && !matches!(self.to_ty, Some(Ty::Field)) {
            return Err("ZConstLiteralRewriter: Field type mismatch"
                .to_string()
                .into());
        }
        walk_field_type(self, fty)
    }

    fn visit_boolean_type(&mut self, bty: &mut ast::BooleanType<'ast>) -> ZVisitorResult {
        if self.to_ty.is_some() && !matches!(self.to_ty, Some(Ty::Bool)) {
            return Err("ZConstLiteralRewriter: Bool type mismatch"
                .to_string()
                .into());
        }
        walk_boolean_type(self, bty)
    }

    fn visit_u8_type(&mut self, u8ty: &mut ast::U8Type<'ast>) -> ZVisitorResult {
        if self.to_ty.is_some() && !matches!(self.to_ty, Some(Ty::Uint(8))) {
            return Err("ZConstLiteralRewriter: u8 type mismatch".to_string().into());
        }
        walk_u8_type(self, u8ty)
    }

    fn visit_u16_type(&mut self, u16ty: &mut ast::U16Type<'ast>) -> ZVisitorResult {
        if self.to_ty.is_some() && !matches!(self.to_ty, Some(Ty::Uint(16))) {
            return Err("ZConstLiteralRewriter: u16 type mismatch"
                .to_string()
                .into());
        }
        walk_u16_type(self, u16ty)
    }

    fn visit_u32_type(&mut self, u32ty: &mut ast::U32Type<'ast>) -> ZVisitorResult {
        if self.to_ty.is_some() && !matches!(self.to_ty, Some(Ty::Uint(32))) {
            return Err("ZConstLiteralRewriter: u32 type mismatch"
                .to_string()
                .into());
        }
        walk_u32_type(self, u32ty)
    }

    fn visit_u64_type(&mut self, u64ty: &mut ast::U64Type<'ast>) -> ZVisitorResult {
        if self.to_ty.is_some() && !matches!(self.to_ty, Some(Ty::Uint(64))) {
            return Err("ZConstLiteralRewriter: u64 type mismatch"
                .to_string()
                .into());
        }
        walk_u64_type(self, u64ty)
    }
}
