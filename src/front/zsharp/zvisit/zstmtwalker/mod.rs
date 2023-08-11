//! AST Walker for zokrates_pest_ast

mod zexprtyper;

use super::super::term::Ty;
use super::super::{span_to_string, ZGen};
use super::eqtype::*;
use super::walkfns::*;
use super::{
    bos_to_type, ZConstLiteralRewriter, ZResult, ZVisitorError, ZVisitorMut, ZVisitorResult,
};
use zexprtyper::ZExpressionTyper;

use std::collections::HashMap;
use zokrates_pest_ast as ast;

pub(in super::super) struct ZStatementWalker<'ast, 'ret> {
    rets: &'ret [ast::Type<'ast>],
    gens: &'ret [ast::IdentifierExpression<'ast>],
    zgen: &'ret ZGen<'ast>,
    vars: Vec<HashMap<String, ast::Type<'ast>>>,
}

impl<'ast, 'ret> ZStatementWalker<'ast, 'ret> {
    pub(in super::super) fn new(
        prms: &'ret [ast::Parameter<'ast>],
        rets: &'ret [ast::Type<'ast>],
        gens: &'ret [ast::IdentifierExpression<'ast>],
        zgen: &'ret ZGen<'ast>,
    ) -> Self {
        let vars = vec![prms
            .iter()
            .map(|p| (p.id.value.clone(), p.ty.clone()))
            .collect()];
        Self {
            rets,
            gens,
            zgen,
            vars,
        }
    }

    fn eq_type(&self, ty: &ast::Type<'ast>, ty2: &ast::Type<'ast>) -> ZVisitorResult {
        eq_type(ty, ty2, self.zgen)
    }

    fn type_expression<'wlk>(
        &self,
        expr: &mut ast::Expression<'ast>,
        zty: &mut ZExpressionTyper<'ast, 'ret, 'wlk>,
    ) -> ZResult<Option<ast::Type<'ast>>> {
        zty.visit_expression(expr)?;
        zty.take()?
            .map(|to_ty| self.unify_expression(to_ty.clone(), expr).map(|()| to_ty))
            .transpose()
    }

    // XXX(opt) take ref to Type instead of owned?
    fn unify(
        &self,
        ty: Option<ast::Type<'ast>>,
        expr: &mut ast::Expression<'ast>,
    ) -> ZVisitorResult {
        // start with the simple constant literal rewrites
        let mut rewriter = ZConstLiteralRewriter::new(None);
        rewriter.visit_expression(expr)?;
        ty.map(|ty| self.unify_expression(ty, expr))
            .unwrap_or(Ok(()))
    }

    fn unify_expression(
        &self,
        ty: ast::Type<'ast>,
        expr: &mut ast::Expression<'ast>,
    ) -> ZVisitorResult {
        use ast::Expression::*;
        let ty = self.canon_type(ty)?;
        match expr {
            Ternary(te) => self.unify_ternary(ty, te),
            Binary(be) => self.unify_binary(ty, be),
            Unary(ue) => self.unify_unary(ty, ue),
            Postfix(pe) => self.unify_postfix(ty, pe),
            Identifier(ie) => self.unify_identifier(ty, ie),
            Literal(le) => self.unify_literal(ty, le),
            InlineArray(ia) => self.unify_inline_array(ty, ia),
            InlineStruct(is) => self.unify_inline_struct(ty, is),
            ArrayInitializer(ai) => self.unify_array_initializer(ty, ai),
        }
    }

    fn get_call_ty(
        &self,
        fdef: &ast::FunctionDefinition<'ast>,
        call: &mut ast::CallAccess<'ast>,
        rty: Option<&ast::Type<'ast>>,
    ) -> ZResult<ast::Type<'ast>> {
        // basic consistency checks on Call access
        if call.arguments.expressions.len() != fdef.parameters.len() {
            return Err(format!(
                "ZStatementWalker: wrong number of arguments to fn {}:\n{}",
                &fdef.id.value,
                span_to_string(&call.span),
            )
            .into());
        }
        if fdef.generics.is_empty() && call.explicit_generics.is_some() {
            return Err(format!(
                "ZStatementWalker: got explicit generics for non-generic fn call {}:\n{}",
                &fdef.id.value,
                span_to_string(&call.span),
            )
            .into());
        }
        if call
            .explicit_generics
            .as_ref()
            .map(|eg| eg.values.len() != fdef.generics.len())
            .unwrap_or(false)
        {
            return Err(format!(
                "ZStatementWalker: wrong number of generic args to fn {}:\n{}",
                &fdef.id.value,
                span_to_string(&call.span),
            )
            .into());
        }

        // unify args
        fdef.parameters
            .iter()
            .map(|pty| pty.ty.clone())
            .zip(call.arguments.expressions.iter_mut())
            .try_for_each(|(pty, arg)| self.unify_expression(pty, arg))?;

        let ret_ty = fdef.returns.first().cloned().unwrap_or({
            ast::Type::Basic(ast::BasicType::Boolean(ast::BooleanType {
                span: call.span,
            }))
        });
        if let Some(ty) = rty {
            self.eq_type(ty, &ret_ty)?;
        }
        Ok(ret_ty)
    }

    fn get_postfix_ty(
        &self,
        pf: &mut ast::PostfixExpression<'ast>,
        rty: Option<&ast::Type<'ast>>,
    ) -> ZResult<ast::Type<'ast>> {
        use ast::Access::*;
        assert!(!pf.accesses.is_empty());

        // XXX(assume) no functions in arrays or structs
        // handle first access, which is special because only this one could be a Call()
        let (id, acc) = (&pf.id, &mut pf.accesses);
        let alen = acc.len();
        let (pf_id_ty, acc_offset) = if let Call(ca) = acc.first_mut().unwrap() {
            // look up function type
            self.get_function(&id.value).and_then(|fdef| {
                if fdef.returns.is_empty() {
                    // XXX(unimpl) fn without return type not supported
                    Err(ZVisitorError(format!(
                        "ZStatementWalker: fn {} has no return type",
                        &id.value,
                    )))
                } else if fdef.returns.len() > 1 {
                    // XXX(unimpl) multiple return types not implemented
                    Err(ZVisitorError(format!(
                        "ZStatementWalker: fn {} has multiple returns",
                        &id.value,
                    )))
                } else {
                    let rty = if alen == 1 { rty } else { None };
                    Ok((self.get_call_ty(fdef, ca, rty)?, 1))
                }
            })?
        } else {
            // just look up variable type
            (self.lookup_type(id)?, 0)
        };

        // typecheck the remaining accesses
        self.walk_accesses(pf_id_ty, &pf.accesses[acc_offset..], acc_to_msacc)
    }

    fn unify_postfix(
        &self,
        ty: ast::Type<'ast>,
        pf: &mut ast::PostfixExpression<'ast>,
    ) -> ZVisitorResult {
        let acc_ty = self.get_postfix_ty(pf, Some(&ty))?;
        self.eq_type(&ty, &acc_ty)
    }

    fn unify_array_initializer(
        &self,
        ty: ast::Type<'ast>,
        ai: &mut ast::ArrayInitializerExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::Type::*;
        let mut at = if let Array(at) = ty {
            at
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: array initializer expression wanted type {:?}:\n{}",
                &ty,
                span_to_string(&ai.span),
            )));
        };
        assert!(!at.dimensions.is_empty());

        // XXX(unimpl) does not check array lengths, just unifies ai.count with U32!
        let u32_ty = Basic(ast::BasicType::U32(ast::U32Type { span: ai.span }));
        self.unify_expression(u32_ty, &mut ai.count)?;

        let arr_ty = if at.dimensions.len() > 1 {
            at.dimensions.remove(0); // perf?
            Array(at)
        } else {
            bos_to_type(at.ty)
        };
        self.unify_expression(arr_ty, &mut ai.value)
    }

    fn unify_inline_struct(
        &self,
        ty: ast::Type<'ast>,
        is: &mut ast::InlineStructExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::Type::*;
        let st = if let Struct(st) = ty {
            st
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: inline struct wanted type {:?}:\n{}",
                &ty,
                span_to_string(&is.span),
            )));
        };

        let mut sm_types = self
            .get_struct_or_type(&st.id.value)?
            .expect("type aliases should have been flattened already")
            .fields
            .iter()
            .map(|sf| (sf.id.value.clone(), sf.ty.clone()))
            .collect::<HashMap<String, ast::Type<'ast>>>();

        // unify each InlineStructExpression member with field def from struct def'n
        is.members.iter_mut().try_for_each(|ism| {
            sm_types
                .remove(ism.id.value.as_str())
                .ok_or_else(|| {
                    ZVisitorError(format!(
                        "ZStatementWalker: struct {} has no member {}, or duplicate member in expression",
                        &st.id.value, &ism.id.value,
                    ))
                })
                .and_then(|sm_ty| self.unify_expression(sm_ty, &mut ism.expression))
        })?;

        // make sure InlineStructExpression declared all members
        if !sm_types.is_empty() {
            Err(ZVisitorError(format!(
                "ZStatementWalker: struct {} inline decl missing members {:?}\n",
                &st.id.value,
                sm_types.keys().collect::<Vec<_>>()
            )))
        } else {
            Ok(())
        }
    }

    fn unify_inline_array(
        &self,
        ty: ast::Type<'ast>,
        ia: &mut ast::InlineArrayExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::{SpreadOrExpression::*, Type::*};
        let at = if let Array(at) = ty {
            at
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: inline array wanted type {:?}:\n{}",
                &ty,
                span_to_string(&ia.span),
            )));
        };

        // XXX(unimpl) does not check array lengths, just checks contained types!
        let exp_ty = if at.dimensions.len() == 1 {
            bos_to_type(at.ty.clone())
        } else {
            ast::Type::Array(ast::ArrayType {
                ty: at.ty.clone(),
                dimensions: Vec::from(&at.dimensions[1..]),
                span: at.span,
            })
        };
        ia.expressions.iter_mut().try_for_each(|soe| match soe {
            Spread(s) => self.unify_expression(Array(at.clone()), &mut s.expression),
            Expression(e) => self.unify_expression(exp_ty.clone(), e),
        })
    }

    fn unify_identifier(
        &self,
        ty: ast::Type<'ast>,
        ie: &ast::IdentifierExpression<'ast>,
    ) -> ZVisitorResult {
        self.lookup_type(ie).and_then(|ity| self.eq_type(&ty, &ity))
    }

    fn unify_ternary(
        &self,
        ty: ast::Type<'ast>,
        te: &mut ast::TernaryExpression<'ast>,
    ) -> ZVisitorResult {
        // first expr must have type Bool, others the expected output type
        let bool_ty = ast::Type::Basic(ast::BasicType::Boolean(ast::BooleanType { span: te.span }));
        self.unify_expression(bool_ty, &mut te.first)?;
        self.unify_expression(ty.clone(), &mut te.second)?;
        self.unify_expression(ty, &mut te.third)
    }

    fn unify_binary(
        &self,
        ty: ast::Type<'ast>,
        be: &mut ast::BinaryExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::{BasicType::*, BinaryOperator::*, Type::*};
        let bt = if let Basic(bt) = ty {
            bt
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: binary operators require Basic operands:\n{}",
                span_to_string(&be.span),
            )));
        };

        let (lt, rt) = match &be.op {
            BitXor | BitAnd | BitOr => match &bt {
                U8(_) | U16(_) | U32(_) | U64(_) => Ok((Basic(bt.clone()), Basic(bt))),
                _ => Err(ZVisitorError(
                    "ZStatementWalker: Bit/Rem operators require U* operands".to_owned(),
                )),
            },
            RightShift | LeftShift => match &bt {
                U8(_) | U16(_) | U32(_) | U64(_) => {
                    Ok((Basic(bt), Basic(U32(ast::U32Type { span: be.span }))))
                }
                _ => Err(ZVisitorError(
                    "ZStatementWalker: << and >> operators require U* left operand".to_owned(),
                )),
            },
            Or | And => match &bt {
                Boolean(_) => Ok((Basic(bt.clone()), Basic(bt))),
                _ => Err(ZVisitorError(
                    "ZStatementWalker: Logical-And/Or operators require Bool operands".to_owned(),
                )),
            },
            Add | Sub | Mul | Div | Rem => match &bt {
                Boolean(_) => Err(ZVisitorError(
                    "ZStatementWalker: +,-,*,/ operators require Field or U* operands".to_owned(),
                )),
                _ => Ok((Basic(bt.clone()), Basic(bt))),
            },
            Eq | NotEq | Lt | Gt | Lte | Gte => match &bt {
                Boolean(_) => {
                    let mut expr_walker = ZExpressionTyper::new(self);
                    let lty = self.type_expression(&mut be.left, &mut expr_walker)?;
                    let rty = self.type_expression(&mut be.right, &mut expr_walker)?;
                    match (&lty, &rty) {
                        (Some(lt), None) if matches!(lt, Basic(_)) || matches!(&be.op, Eq | NotEq) =>
                            Ok((lty.clone().unwrap(), lty.unwrap())),
                        (None, Some(rt)) if matches!(rt, Basic(_)) || matches!(&be.op, Eq | NotEq) =>
                            Ok((rty.clone().unwrap(), rty.unwrap())),
                        (Some(lt), Some(rt)) if (matches!(lt, Basic(_)) && matches!(rt, Basic(_))) || matches!(&be.op, Eq | NotEq) => {
                            let lty = lty.unwrap();
                            let rty = rty.unwrap();
                            self.eq_type(&lty, &rty)
                                .map_err(|e|
                                ZVisitorError(format!(
                                    "ZStatementWalker: got differing types {:?}, {:?} for lhs, rhs of expr:\n{}\n{}",
                                    &lty,
                                    &rty,
                                    e.0,
                                    span_to_string(&be.span),
                                )))
                                .map(|_| (lty, rty))
                        }
                        (None, None) => Err(ZVisitorError(format!(
                            "ZStatementWalker: could not infer type of binop:\n{}",
                            span_to_string(&be.span),
                        ))),
                        _ => Err(ZVisitorError(format!(
                            "ZStatementWalker: unknown error in binop typing:\n{}",
                            span_to_string(&be.span),
                        ))),
                    }
                    .and_then(|(lty, rty)| if matches!(&be.op, Lt | Gt | Lte | Gte) && matches!(lty, Basic(Boolean(_))) {
                        Err(ZVisitorError(format!(
                            "ZStatementWalker: >,>=,<,<= operators cannot be applied to Bool:\n{}",
                            span_to_string(&be.span),
                        )))
                    } else {
                        Ok((lty, rty))
                    })
                }
                _ => Err(ZVisitorError(
                    "ZStatementWalker: comparison and equality operators output Bool".to_owned(),
                )),
            },
            Pow => match &bt {
                // XXX does POW operator really require U32 RHS?
                Field(_) => Ok((Basic(bt), Basic(U32(ast::U32Type { span: be.span })))),
                _ => Err(ZVisitorError(
                    "ZStatementWalker: pow operator must take Field LHS and U32 RHS".to_owned(),
                )),
            },
        }?;
        self.unify_expression(lt, &mut be.left)?;
        self.unify_expression(rt, &mut be.right)
    }

    fn unify_unary(
        &self,
        ty: ast::Type<'ast>,
        ue: &mut ast::UnaryExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::{BasicType::*, Type::*, UnaryOperator::*};
        // strict operator applies to any type; expression has same type
        if let Strict(_) = &ue.op {
            return self.unify_expression(ty, &mut ue.expression);
        }

        // remaining unary operators can only take Basic types
        let bt = if let Basic(bt) = ty {
            bt
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: unary operators require Basic operands:\n{}",
                span_to_string(&ue.span),
            )));
        };

        let ety = match &ue.op {
            Pos(_) | Neg(_) => match &bt {
                Boolean(_) => Err(ZVisitorError(
                    "ZStatementWalker: +,- unary operators require Field or U* operands"
                        .to_string(),
                )),
                _ => Ok(Basic(bt)),
            },
            Not(_) => match &bt {
                Field(_) => Err(ZVisitorError(
                    "ZStatementWalker: ! unary operator requires U* or Bool operand".to_string(),
                )),
                _ => Ok(Basic(bt)),
            },
            Strict(_) => unreachable!(),
        }?;

        self.unify_expression(ety, &mut ue.expression)
    }

    fn unify_literal(
        &self,
        ty: ast::Type<'ast>,
        le: &mut ast::LiteralExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::{BasicType::*, LiteralExpression::*, Type::*};
        let bt = if let Basic(bt) = ty {
            bt
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: literal expressions must yield basic types:\n{}",
                span_to_string(le.span()),
            )));
        };

        match le {
            BooleanLiteral(_) => {
                if let Boolean(_) = &bt {
                    Ok(())
                } else {
                    Err(ZVisitorError(format!(
                        "ZStatementWalker: expected {:?}, found BooleanLiteral:\n{}",
                        &bt,
                        span_to_string(le.span()),
                    )))
                }
            }
            HexLiteral(hle) => {
                use ast::HexNumberExpression as HNE;
                match &hle.value {
                    HNE::U8(_) if matches!(&bt, U8(_)) => Ok(()),
                    HNE::U16(_) if matches!(&bt, U16(_)) => Ok(()),
                    HNE::U32(_) if matches!(&bt, U32(_)) => Ok(()),
                    HNE::U64(_) if matches!(&bt, U64(_)) => Ok(()),
                    _ => Err(ZVisitorError(format!(
                        "ZStatementWalker: HexLiteral seemed to want type {:?}:\n{}",
                        &bt,
                        span_to_string(&hle.span),
                    ))),
                }
            }
            DecimalLiteral(dle) => {
                use ast::DecimalSuffix as DS;
                match &dle.suffix {
                    Some(ds) => match (ds, &bt) {
                        (DS::Field(_), Field(_)) => Ok(()),
                        (DS::U8(_), U8(_)) => Ok(()),
                        (DS::U16(_), U16(_)) => Ok(()),
                        (DS::U32(_), U32(_)) => Ok(()),
                        (DS::U64(_), U64(_)) => Ok(()),
                        _ => Err(ZVisitorError(format!(
                            "ZStatementWalker: DecimalLiteral wanted {:?} found {:?}:\n{}",
                            &bt,
                            ds,
                            span_to_string(&dle.span),
                        ))),
                    },
                    None => match &bt {
                        Boolean(_) => Err(ZVisitorError(format!(
                            "ZStatementWalker: DecimalLiteral wanted Bool:\n{}",
                            span_to_string(&dle.span),
                        ))),
                        Field(_) => Ok(DS::Field(ast::FieldSuffix { span: dle.span })),
                        U8(_) => Ok(DS::U8(ast::U8Suffix { span: dle.span })),
                        U16(_) => Ok(DS::U16(ast::U16Suffix { span: dle.span })),
                        U32(_) => Ok(DS::U32(ast::U32Suffix { span: dle.span })),
                        U64(_) => Ok(DS::U64(ast::U64Suffix { span: dle.span })),
                    }
                    .map(|ds| {
                        dle.suffix.replace(ds);
                    }),
                }
            }
        }
    }

    fn walk_accesses<F, T>(
        &self,
        mut ty: ast::Type<'ast>,
        accs: &[T],
        f: F,
    ) -> ZResult<ast::Type<'ast>>
    where
        F: Fn(&T) -> ZResult<MSAccRef<'_, 'ast>>,
    {
        use ast::Type;
        use MSAccRef::*;
        let mut acc_dim_offset = 0;
        for acc in accs {
            if matches!(ty, Type::Basic(_)) {
                return Err(ZVisitorError(
                    "ZStatementWalker: tried to walk accesses into a Basic type".to_string(),
                ));
            }
            ty = self.canon_type(ty)?;
            ty = match f(acc)? {
                Select(aacc) => {
                    if let Type::Array(aty) = ty {
                        use ast::RangeOrExpression::*;
                        match &aacc.expression {
                            Range(_) => Type::Array(aty),
                            Expression(_) => {
                                if aty.dimensions.len() - acc_dim_offset > 1 {
                                    acc_dim_offset += 1;
                                    Type::Array(aty)
                                } else {
                                    acc_dim_offset = 0;
                                    bos_to_type(aty.ty)
                                }
                            }
                        }
                    } else {
                        return Err(ZVisitorError(
                            "ZStatementWalker: tried to access an Array as a Struct".to_string(),
                        ));
                    }
                }
                Member(macc) => {
                    // XXX(unimpl) LHS of definitions must make generics explicit
                    if let Type::Struct(sty) = ty {
                        self.get_struct_or_type(&sty.id.value)?
                            .expect("type aliases should have been flattened already")
                            .fields
                            .iter()
                            .find(|f| f.id.value == macc.id.value)
                            .ok_or_else(|| {
                                ZVisitorError(format!(
                                    "ZStatementWalker: struct {} has no member {}",
                                    &sty.id.value, &macc.id.value,
                                ))
                            })
                            .map(|f| f.ty.clone())?
                    } else {
                        return Err(ZVisitorError(
                            "ZStatementWalker: tried to access a Struct as an Array".to_string(),
                        ));
                    }
                }
            }
        }

        // handle any dimensional readjustments we've delayed
        if acc_dim_offset > 0 {
            ty = if let Type::Array(mut aty) = ty {
                Type::Array(ast::ArrayType {
                    ty: aty.ty,
                    dimensions: aty.dimensions.drain(acc_dim_offset..).collect(),
                    span: aty.span,
                })
            } else {
                unreachable!("acc_dim_offset != 0 when ty not Array");
            }
        }

        Ok(ty)
    }

    fn get_function(&self, id: &str) -> ZResult<&ast::FunctionDefinition<'ast>> {
        self.zgen
            .get_function(id)
            .ok_or_else(|| ZVisitorError(format!("ZStatementWalker: undeclared function {id}")))
    }

    fn get_struct_or_type(
        &self,
        id: &str,
    ) -> ZResult<Result<&ast::StructDefinition<'ast>, &ast::TypeDefinition<'ast>>> {
        self.zgen
            .get_struct_or_type(id)
            .map(|(m, _)| m)
            .ok_or_else(|| {
                ZVisitorError(format!("ZStatementWalker: undeclared struct type {id}.\nNOTE: If {id} is a struct behind an imported type alias, its definition\n      must also be imported into the module where the alias is used."))
            })
    }

    fn const_defined(&self, id: &str) -> bool {
        self.zgen.const_defined(id)
    }

    fn generic_defined(&self, id: &str) -> bool {
        // XXX(perf) if self.gens is long this could be improved with a HashSet.
        // Realistically, a function will have a small number of generic params.
        self.gens.iter().any(|g| g.value == id)
    }

    fn var_defined(&self, id: &str) -> bool {
        self.vars.iter().rev().any(|v| v.contains_key(id))
    }

    fn lookup_var(&self, nm: &str) -> Option<ast::Type<'ast>> {
        self.vars.iter().rev().find_map(|v| v.get(nm).cloned())
    }

    fn lookup_type(&self, id: &ast::IdentifierExpression<'ast>) -> ZResult<ast::Type<'ast>> {
        if self.generic_defined(&id.value) {
            // generics are always U32
            Ok(ast::Type::Basic(ast::BasicType::U32(ast::U32Type {
                span: id.span,
            })))
        } else if let Some(t) = self.zgen.const_ty_lookup_(&id.value) {
            Ok(t.clone())
        } else {
            self.lookup_var(&id.value).ok_or_else(|| {
                ZVisitorError(format!(
                    "ZStatementWalker: identifier {} undefined",
                    &id.value
                ))
            })
        }
    }

    fn apply_varonly<F, R>(&mut self, nm: &str, f: F) -> ZResult<R>
    where
        F: FnOnce(&mut Self, &str) -> R,
    {
        if self.generic_defined(nm) {
            Err(ZVisitorError(format!(
                "ZStatementWalker: attempted to shadow generic {nm}"
            )))
        } else if self.const_defined(nm) {
            Err(ZVisitorError(format!(
                "ZStatementWalker: attempted to shadow const {nm}"
            )))
        } else {
            Ok(f(self, nm))
        }
    }

    fn lookup_type_varonly(&mut self, nm: &str) -> ZResult<Option<ast::Type<'ast>>> {
        self.apply_varonly(nm, |s, nm| s.lookup_var(nm))
    }

    fn insert_var(&mut self, nm: &str, ty: ast::Type<'ast>) -> ZResult<Option<ast::Type<'ast>>> {
        self.apply_varonly(nm, |s, nm| {
            s.vars.last_mut().unwrap().insert(nm.to_string(), ty)
        })
    }

    fn push_scope(&mut self) {
        self.vars.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.vars.pop();
    }

    // shallow canonicalization: flatten down to the first Basic, Array, or non-alias Struct
    fn canon_type(&self, ty: ast::Type<'ast>) -> ZResult<ast::Type<'ast>> {
        use ast::Type::*;
        match ty {
            Basic(b) => Ok(ast::Type::Basic(b)),
            Array(a) => Ok(ast::Type::Array(a)),
            Struct(s) => match self.get_struct_or_type(&s.id.value)? {
                Ok(_) => Ok(ast::Type::Struct(s)),
                Err(tydef) => self.canon_type(tydef.ty.clone()),
            },
        }
    }
}

impl<'ast, 'ret> ZVisitorMut<'ast> for ZStatementWalker<'ast, 'ret> {
    fn visit_return_statement(&mut self, ret: &mut ast::ReturnStatement<'ast>) -> ZVisitorResult {
        if self.rets.len() != ret.expressions.len() {
            return Err(ZVisitorError(
                "ZStatementWalker: mismatched return expression/type".to_owned(),
            ));
        }

        // XXX(unimpl) multi-return statements not supported
        if self.rets.len() > 1 {
            return Err(ZVisitorError(
                "ZStatementWalker: multi-returns not supported".to_owned(),
            ));
        }

        if let Some(expr) = ret.expressions.first_mut() {
            self.unify(self.rets.first().cloned(), expr)?;
        }
        walk_return_statement(self, ret)
    }

    fn visit_assertion_statement(
        &mut self,
        asrt: &mut ast::AssertionStatement<'ast>,
    ) -> ZVisitorResult {
        let bool_ty = ast::Type::Basic(ast::BasicType::Boolean(ast::BooleanType {
            span: asrt.span,
        }));
        self.unify(Some(bool_ty), &mut asrt.expression)?;
        walk_assertion_statement(self, asrt)
    }

    fn visit_cond_store_statement(
        &mut self,
        s: &mut ast::CondStoreStatement<'ast>,
    ) -> ZVisitorResult {
        let bool_ty = ast::Type::Basic(ast::BasicType::Boolean(ast::BooleanType { span: s.span }));
        self.unify(Some(bool_ty), &mut s.condition)?;
        walk_cond_store_statement(self, s)
    }

    fn visit_iteration_statement(
        &mut self,
        iter: &mut ast::IterationStatement<'ast>,
    ) -> ZVisitorResult {
        self.visit_type(&mut iter.ty)?;

        self.push_scope(); // {
        self.insert_var(&iter.index.value, iter.ty.clone())?;
        self.visit_identifier_expression(&mut iter.index)?;

        // type propagation for index expressions
        self.unify(Some(iter.ty.clone()), &mut iter.from)?;
        self.visit_expression(&mut iter.from)?;
        self.unify(Some(iter.ty.clone()), &mut iter.to)?;
        self.visit_expression(&mut iter.to)?;

        iter.statements
            .iter_mut()
            .try_for_each(|s| self.visit_statement(s))?;

        self.pop_scope(); // }
        self.visit_span(&mut iter.span)
    }

    fn visit_definition_statement(
        &mut self,
        def: &mut ast::DefinitionStatement<'ast>,
    ) -> ZVisitorResult {
        // XXX(unimpl) no L<-R generic inference right now.
        // REVISIT: if LHS is generic typed identifier and RHS has complete type, infer L<-R?
        def.lhs
            .iter_mut()
            .try_for_each(|l| self.visit_typed_identifier_or_assignee(l))?;

        // unify lhs and rhs
        // XXX(unimpl) multi-LHS statements not supported
        if def.lhs.len() > 1 {
            return Err(ZVisitorError(
                "ZStatementWalker: multi-LHS assignments not supported".to_owned(),
            ));
        }
        let ty_accs = def
            .lhs
            .first()
            .map(|tioa| {
                use ast::TypedIdentifierOrAssignee::*;
                let (na, acc) = match tioa {
                    Assignee(a) => (&a.id.value, a.accesses.as_ref()),
                    TypedIdentifier(ti) => (&ti.identifier.value, &[][..]),
                };
                self.lookup_type_varonly(na).map(|t| t.map(|t| (t, acc)))
            })
            .transpose()?
            .flatten();
        if let Some((ty, accs)) = ty_accs {
            let ty = self.walk_accesses(ty, accs, aacc_to_msacc)?;
            self.unify(Some(ty), &mut def.expression)?;
        } else {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: found expression with no LHS:\n{}",
                span_to_string(&def.span),
            )));
        }
        self.visit_expression(&mut def.expression)?;
        self.visit_span(&mut def.span)
    }

    fn visit_assignee(&mut self, asgn: &mut ast::Assignee<'ast>) -> ZVisitorResult {
        if !self.var_defined(&asgn.id.value) {
            Err(ZVisitorError(format!(
                "ZStatementWalker: assignment to undeclared variable {}",
                &asgn.id.value
            )))
        } else {
            walk_assignee(self, asgn)
        }
    }

    fn visit_typed_identifier(&mut self, ti: &mut ast::TypedIdentifier<'ast>) -> ZVisitorResult {
        ZConstLiteralRewriter::new(None).visit_type(&mut ti.ty)?;
        self.insert_var(&ti.identifier.value, ti.ty.clone())?;
        walk_typed_identifier(self, ti)
    }

    fn visit_range_or_expression(
        &mut self,
        roe: &mut ast::RangeOrExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::RangeOrExpression::*;
        match roe {
            Range(r) => self.visit_range(r),
            Expression(e) => self.visit_array_index_expression(e),
        }
    }

    fn visit_array_index_expression(&mut self, e: &mut ast::Expression<'ast>) -> ZVisitorResult {
        let mut zty = ZExpressionTyper::new(self);
        if self.type_expression(e, &mut zty)?.is_none() {
            let mut zrw = ZConstLiteralRewriter::new(Some(Ty::Field));
            zrw.visit_expression(e)?;
        }
        self.visit_expression(e)
    }

    fn visit_range(&mut self, rng: &mut ast::Range<'ast>) -> ZVisitorResult {
        let mut zty = ZExpressionTyper::new(self);
        let fty = rng
            .from
            .as_mut()
            .map(|fexp| self.type_expression(&mut fexp.0, &mut zty))
            .transpose()?
            .flatten();
        let tty = rng
            .to
            .as_mut()
            .map(|texp| self.type_expression(&mut texp.0, &mut zty))
            .transpose()?
            .flatten();
        match (fty, tty) {
            (None, None) => {
                let mut zrw = ZConstLiteralRewriter::new(Some(Ty::Field));
                rng.from
                    .as_mut()
                    .map(|fexp| zrw.visit_expression(&mut fexp.0))
                    .transpose()?;
                rng.to
                    .as_mut()
                    .map(|texp| zrw.visit_expression(&mut texp.0))
                    .transpose()?;
                Ok(())
            }
            (Some(fty), None) => rng
                .to
                .as_mut()
                .map(|texp| self.unify_expression(fty, &mut texp.0))
                .unwrap_or(Ok(())),
            (None, Some(tty)) => rng
                .from
                .as_mut()
                .map(|fexp| self.unify_expression(tty, &mut fexp.0))
                .unwrap_or(Ok(())),
            (Some(fty), Some(tty)) => self.eq_type(&fty, &tty).map_err(|e| {
                ZVisitorError(format!(
                    "typing Range: {}\n{}",
                    e.0,
                    span_to_string(&rng.span),
                ))
            }),
        }?;
        self.visit_span(&mut rng.span)
    }
}

enum MSAccRef<'a, 'ast> {
    Select(&'a ast::ArrayAccess<'ast>),
    Member(&'a ast::MemberAccess<'ast>),
}

fn aacc_to_msacc<'a, 'ast>(i: &'a ast::AssigneeAccess<'ast>) -> ZResult<MSAccRef<'a, 'ast>> {
    use ast::AssigneeAccess::*;
    Ok(match i {
        Select(t) => MSAccRef::Select(t),
        Member(t) => MSAccRef::Member(t),
    })
}

fn acc_to_msacc<'a, 'ast>(i: &'a ast::Access<'ast>) -> ZResult<MSAccRef<'a, 'ast>> {
    use ast::Access::*;
    match i {
        Select(t) => Ok(MSAccRef::Select(t)),
        Member(t) => Ok(MSAccRef::Member(t)),
        Call(t) => Err(ZVisitorError(format!(
            "Illegal fn call:\n{}",
            span_to_string(&t.span),
        ))),
    }
}
