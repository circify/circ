//! AST Walker for zokrates_pest_ast

mod eqtype;
mod zexprrewriter;
mod zexprtyper;

use eqtype::*;
use zexprrewriter::ZExpressionRewriter;
use zexprtyper::ZExpressionTyper;
use super::walkfns::*;
use super::{ZConstLiteralRewriter, ZVisitorMut, ZVisitorError, ZVisitorResult, ZResult};
use super::super::term::{const_int, const_int_ref, Ty};
use super::super::{ZGen, span_to_string};

use std::collections::HashMap;
use zokrates_pest_ast as ast;

fn bos_to_type<'ast>(bos: ast::BasicOrStructType<'ast>) -> ast::Type<'ast> {
    use ast::{BasicOrStructType::*, Type};
    match bos {
        Struct(st) => Type::Struct(st),
        Basic(bt) => Type::Basic(bt),
    }
}

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
        zgen: &'ret mut ZGen<'ast>,
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

    fn type_expression<'wlk>(
        &self,
        expr: &mut ast::Expression<'ast>,
        zty: &mut ZExpressionTyper<'ast, 'ret, 'wlk>,
    ) -> ZResult<Option<ast::Type<'ast>>> {
        zty.visit_expression(expr)?;
        zty.take()
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
        ty.map(|ty| self.unify_expression(ty, expr)).unwrap_or(Ok(()))
    }

    fn unify_expression(
        &self,
        ty: ast::Type<'ast>,
        expr: &mut ast::Expression<'ast>,
    ) -> ZVisitorResult {
        use ast::Expression::*;
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

    fn fdef_gen_ty(
        &self,
        dty: &ast::Type<'ast>,      // declared type (from fn defn)
        rty: &ast::Type<'ast>,      // required type (from call context)
        egv: &mut Vec<ast::ConstantGenericValue<'ast>>,
        gid_map: &HashMap<&str, usize>,
    ) -> ZVisitorResult {
        use ast::Type::*;
        match (dty, rty) {
            (Basic(dty_b), Basic(rty_b)) => eq_basic_type(dty_b, rty_b)
                .map_err(|e| ZVisitorError(format!("Inferring generic fn call: {}", e.0))),
            (Array(dty_a), Array(rty_a)) => self.fdef_gen_ty_array(dty_a, rty_a, egv, gid_map),
            (Struct(dty_s), Struct(rty_s)) => self.fdef_gen_ty_struct(dty_s, rty_s, egv, gid_map),
            _ => Err(ZVisitorError(format!(
                "Inferring generic fn call: type mismatch: expected {:?}, got {:?}",
                rty,
                dty,
            ))),
        }
    }

    fn fdef_gen_ty_array(
        &self,
        dty: &ast::ArrayType<'ast>,     // declared type (from fn defn)
        rty: &ast::ArrayType<'ast>,     // required type (from call context)
        egv: &mut Vec<ast::ConstantGenericValue<'ast>>,
        gid_map: &HashMap<&str, usize>,
    ) -> ZVisitorResult {
        // check dimensions
        if dty.dimensions.len() != rty.dimensions.len() {
            return Err(ZVisitorError(format!(
                "Inferring generic fn call: Array #dimensions mismatch: expected {}, got {}",
                rty.dimensions.len(),
                dty.dimensions.len(),
            )));
        }

        // unify the type contained in the array
        use ast::BasicOrStructType as BoST;
        match (&dty.ty, &rty.ty) {
            (BoST::Struct(dty_s), BoST::Struct(rty_s)) => self.fdef_gen_ty_struct(dty_s, rty_s, egv, gid_map),
            (BoST::Basic(dty_b), BoST::Basic(rty_b)) => eq_basic_type(dty_b, rty_b)
                .map_err(|e| ZVisitorError(format!("Inferring generic fn call: {}", e.0))),
            _ => Err(ZVisitorError(format!(
                "Inferring generic fn call: Array type mismatch: expected {:?}, got {:?}",
                &rty.ty,
                &dty.ty,
            ))),
        }?;

        // unify the dimensions
        dty.dimensions
            .iter()
            .zip(rty.dimensions.iter())
            .try_for_each(|(dexp, rexp)| self.fdef_gen_ty_expr(dexp, rexp, egv, gid_map))
    }

    fn fdef_gen_ty_struct(
        &self,
        dty: &ast::StructType<'ast>,    // declared type (from fn defn)
        rty: &ast::StructType<'ast>,    // required type (from call context)
        egv: &mut Vec<ast::ConstantGenericValue<'ast>>,
        gid_map: &HashMap<&str, usize>,
    ) -> ZVisitorResult {
        if &dty.id.value != &rty.id.value {
            return Err(ZVisitorError(format!(
                "Inferring generic in fn call: wanted struct {}, found struct {}",
                &rty.id.value,
                &dty.id.value,
            )));
        }
        // make sure struct exists and short-circuit if it's not generic
        if self.get_struct(&dty.id.value)?.generics.is_empty() {
            return if dty.explicit_generics.is_some() {
                Err(ZVisitorError(format!(
                    "Inferring generic in fn call: got explicit generics for non-generic struct type {}:\n{}",
                    &dty.id.value,
                    span_to_string(&dty.span),
                )))
            } else {
                Ok(())
            };
        }

        // declared type in fn defn must provide explicit generics
        use ast::ConstantGenericValue::*;
        if dty.explicit_generics
            .as_ref()
            .map(|eg| eg.values.iter().any(|eg| matches!(eg, Underscore(_))))
            .unwrap_or(true)
        {
            return Err(ZVisitorError(format!(
                "Cannot infer generic values for struct {}\nGeneric structs in fn defns must have explicit generics (possibly in terms of fn generics)",
                &dty.id.value,
            )));
        }

        // invariant: rty is LHS, therefore must have explicit generics
        let dty_egvs = &dty.explicit_generics.as_ref().unwrap().values;
        let rty_egvs = &rty.explicit_generics.as_ref().unwrap().values;
        assert_eq!(dty_egvs.len(), rty_egvs.len());

        // unify generic args to structs
        dty_egvs
            .iter()
            .zip(rty_egvs.iter())
            .try_for_each(|(dv, rv)| self.fdef_gen_ty_cgv(dv, rv, egv, gid_map))
    }

    fn fdef_gen_ty_cgv(
        &self,
        dv: &ast::ConstantGenericValue<'ast>,   // declared type (from fn defn)
        rv: &ast::ConstantGenericValue<'ast>,   // required type (from call context)
        egv: &mut Vec<ast::ConstantGenericValue<'ast>>,
        gid_map: &HashMap<&str, usize>,
    ) -> ZVisitorResult {
        use ast::ConstantGenericValue::*;
        match (dv, rv) {
            (Identifier(did), _) => {
                if let Some(&doff) = gid_map.get(did.value.as_str()) {
                    if matches!(&egv[doff], Underscore(_)) {
                        egv[doff] = rv.clone();
                        Ok(())
                    } else {
                        self.fdef_gen_cgv_check(&egv[doff], rv)
                    }
                } else {
                    self.fdef_gen_cgv_check(dv, rv)
                }
            }
            (dv, rv) => self.fdef_gen_cgv_check(dv, rv),
        }
    }

    fn fdef_gen_cgv_check(
        &self,
        dv: &ast::ConstantGenericValue<'ast>,
        rv: &ast::ConstantGenericValue<'ast>,
    ) -> ZVisitorResult {
        use ast::ConstantGenericValue::*;
        match (dv, rv) {
            (Underscore(_), _) | (_, Underscore(_)) => unreachable!(),
            (Value(dle), Value(rle)) => self.fdef_gen_le_le(dle, rle),
            (Identifier(did), Identifier(rid)) => self.fdef_gen_id_id(did, rid),
            (Identifier(did), Value(rle)) => self.fdef_gen_id_le(did, rle),
            (Value(dle), Identifier(rid)) => self.fdef_gen_id_le(rid, dle),
        }
    }

    fn fdef_gen_id_id(
        &self,
        did: &ast::IdentifierExpression<'ast>,
        rid: &ast::IdentifierExpression<'ast>,
    ) -> ZVisitorResult {
        // did must be either generic id in enclosing scope or const
        if self.generic_defined(did.value.as_str()) {
            if &did.value == &rid.value {
                Ok(())
            } else {
                Err(ZVisitorError(format!(
                    "Inconsistent generic args detected: wanted {}, got {}",
                    &rid.value,
                    &did.value,
                )))
            }
        } else if self.generic_defined(rid.value.as_str()) {
            // did is a const, but rid is a generic arg
            Err(ZVisitorError(format!(
                "Generic identifier {} is not identically const identifier {}",
                &rid.value,
                &did.value,
            )))
        } else {
            match (self.zgen.const_lookup_(did.value.as_str()),
                   self.zgen.const_lookup_(rid.value.as_str())) {
                (None, _) => Err(ZVisitorError(format!(
                    "Constant {} undefined when inferring generics",
                    &did.value,
                ))),
                (_, None) => Err(ZVisitorError(format!(
                    "Constant {} undefined when inferring generics",
                    &rid.value,
                ))),
                (Some(dc), Some(rc)) => {
                    let dval = const_int_ref(dc)?;
                    let rval = const_int_ref(rc)?;
                    if dval != rval {
                        Err(ZVisitorError(format!(
                            "Mismatch in struct generic: expected {}, got {}",
                            rval,
                            dval,
                        )))
                    } else {
                        Ok(())
                    }
                }
            }
        }
    }

    fn fdef_gen_id_le(
        &self,
        id: &ast::IdentifierExpression<'ast>,
        le: &ast::LiteralExpression<'ast>,
    ) -> ZVisitorResult {
        if self.generic_defined(id.value.as_str()) {
            Err(ZVisitorError(format!(
                "Inconsistent generic args detected: wanted {:?}, got local generic identifier {}",
                le,
                &id.value,
            )))
        } else if let Some(dc) = self.zgen.const_lookup_(id.value.as_str()) {
            let dval = const_int_ref(dc)?;
            let rval = const_int(self.zgen.literal_(le)?)?;
            if dval != rval {
                Err(ZVisitorError(format!(
                    "Mismatch in struct generic: expected {}, got {}",
                    rval,
                    dval,
                )))
            } else {
                Ok(())
            }
        } else {
            Err(ZVisitorError(format!(
                "Constant {} undefined when inferring generics",
                &id.value,
            )))
        }
    }

    fn fdef_gen_le_le(
        &self,
        dle: &ast::LiteralExpression<'ast>,
        rle: &ast::LiteralExpression<'ast>,
    ) -> ZVisitorResult {
        let dval = const_int(self.zgen.literal_(dle)?)?;
        let rval = const_int(self.zgen.literal_(rle)?)?;
        if dval != rval {
            Err(ZVisitorError(format!(
                "Mismatch in struct generic: expected {}, got {}",
                rval,
                dval,
            )))
        } else {
            Ok(())
        }
    }

    fn fdef_gen_expr_check(
        &self,
        dexp: &ast::Expression<'ast>,
        rexp: &ast::Expression<'ast>,
    ) -> ZVisitorResult {
        match (const_int(self.zgen.const_expr_(dexp)?), const_int(self.zgen.const_expr_(rexp)?)) {
            (Ok(dci), Ok(rci)) => {
                if dci == rci {
                    Ok(())
                } else {
                    Err(ZVisitorError(format!(
                        "Mismatch in struct generic: expected {}, got {}",
                        rci,
                        dci,
                    )))
                }
            }
            _ => Err(ZVisitorError(format!(
                "Inferring fn call generics: unsupported array dimension expr {:?}, expected {:?}",
                dexp,
                rexp,
            )))
        }
    }

    fn fdef_gen_ty_expr(
        &self,
        dexp: &ast::Expression<'ast>,       // declared type (from fn defn)
        rexp: &ast::Expression<'ast>,       // required type (from call context)
        egv: &mut Vec<ast::ConstantGenericValue<'ast>>,
        gid_map: &HashMap<&str, usize>,
    ) -> ZVisitorResult {
        use ast::{Expression::*, ConstantGenericValue as CGV};
        match (dexp, rexp) {
            (Binary(dbin), Binary(rbin)) if dbin.op == rbin.op => {
                // XXX(unimpl) improve support for complex const expression inference?
                self.fdef_gen_ty_expr(dbin.left.as_ref(), rbin.left.as_ref(), egv, gid_map)?;
                self.fdef_gen_ty_expr(dbin.right.as_ref(), rbin.right.as_ref(), egv, gid_map)
            }
            (Identifier(did), _) if matches!(rexp, Identifier(_) | Literal(_)) => {
                if let Some(&doff) = gid_map.get(did.value.as_str()) {
                    if matches!(&egv[doff], CGV::Underscore(_)) {
                        egv[doff] = match rexp {
                            Identifier(rid) => CGV::Identifier(rid.clone()),
                            Literal(rle) => CGV::Value(rle.clone()),
                            _ => unreachable!(),
                        };
                        Ok(())
                    } else {
                        match (&egv[doff], rexp) {
                            (CGV::Identifier(did), Identifier(rid)) => self.fdef_gen_id_id(did, rid),
                            (CGV::Identifier(did), Literal(rle)) => self.fdef_gen_id_le(did, rle),
                            (CGV::Value(dle), Identifier(rid)) => self.fdef_gen_id_le(rid, dle),
                            (CGV::Value(dle), Literal(rle)) => self.fdef_gen_le_le(dle, rle),
                            _ => unreachable!(),
                        }
                    }
                } else {
                    match rexp {
                        Identifier(rid) => self.fdef_gen_id_id(did, rid),
                        Literal(rle) => self.fdef_gen_id_le(did, rle),
                        _ => unreachable!(),
                    }
                }
            }
            (Identifier(did), _) => {
                if let Some(&doff) = gid_map.get(did.value.as_str()) {
                    if matches!(&egv[doff], CGV::Underscore(_)) {
                        const_int(self.zgen.const_expr_(rexp)?)
                            .map_err(|e| ZVisitorError(format!(
                                "Inferring fn call generics: cannot constify expression {:?}: {}",
                                rexp,
                                e
                            )))
                            .and_then(|rval| match rval.to_u32() {
                                Some(rval) => {
                                    let span = rexp.span().clone();
                                    let hne = ast::HexNumberExpression::U32(
                                        ast::U32NumberExpression {
                                            value: format!("0x{:08x}", rval),
                                            span: span.clone(),
                                        }
                                    );
                                    let hle = ast::HexLiteralExpression {
                                        value: hne,
                                        span: span.clone(),
                                    };
                                    egv[doff] = CGV::Value(
                                        ast::LiteralExpression::HexLiteral(hle)
                                    );
                                    Ok(())
                                }
                                None => Err(ZVisitorError(format!(
                                    "Inferring fn call generics: got generic value {} out of u32 range",
                                    rval,
                                ))),
                            })
                    } else {
                        self.fdef_gen_expr_check(dexp, rexp)
                    }
                } else {
                    self.fdef_gen_expr_check(dexp, rexp)
                }
            }
            _ => self.fdef_gen_expr_check(dexp, rexp),
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
            Err(format!(
                "ZStatementWalker: wrong number of arguments to fn {}:\n{}",
                &fdef.id.value,
                span_to_string(&call.span),
            ))?;
        }
        if fdef.generics.is_empty() && call.explicit_generics.is_some() {
            Err(format!(
                "ZStatementWalker: got explicit generics for non-generic fn call {}:\n{}",
                &fdef.id.value,
                span_to_string(&call.span),
            ))?;
        }
        if call.explicit_generics.as_ref().map(|eg| eg.values.len() != fdef.generics.len()).unwrap_or(false) {
            Err(format!(
                "ZStatementWalker: wrong number of generic args to fn {}:\n{}",
                &fdef.id.value,
                span_to_string(&call.span),
            ))?;
        }

        // unify args
        fdef.parameters.iter()
            .map(|pty| pty.ty.clone())
            .zip(call.arguments.expressions.iter_mut())
            .try_for_each(|(pty, arg)| self.unify_expression(pty, arg))?;


        Ok(fdef.returns.first().cloned().unwrap_or_else(||
            ast::Type::Basic(ast::BasicType::Boolean(
                    ast::BooleanType { span: call.span.clone() }
        ))))
    }
        /*
        use ast::ConstantGenericValue::*;
        if call
            .explicit_generics
            .as_ref()
            .map(|eg| eg.values.iter().any(|eg| matches!(eg, Underscore(_))))
            .unwrap_or_else(|| !fdef.generics.is_empty())
        {
            // step 1: construct mutable vector of constant generic values, plus a Name->Posn map
            let (gen, par, ret) = (&fdef.generics, &fdef.parameters, &fdef.returns);
            let gid_map = gen.iter().enumerate().map(|(i,v)| (v.value.as_ref(),i)).collect::<HashMap<&str,usize>>();
            let egv = {
                let (sp, eg) = (&call.span, &mut call.explicit_generics);
                &mut eg.get_or_insert_with(|| ast::ExplicitGenerics {
                    values: vec![Underscore( ast::Underscore { span: sp.clone() } ); gen.len()],
                    span: sp.clone(),
                }).values
            };
            assert_eq!(egv.len(), gen.len());

            // step 2: for each function argument unify type and update cgvs
            let mut zty = ZExpressionTyper::new(self);
            for (exp, pty) in call.arguments.expressions.iter_mut().zip(par.iter().map(|p| &p.ty)) {
                let aty = self.type_expression(exp, &mut zty)?;
                if let Some(aty) = aty {
                    self.fdef_gen_ty(pty, &aty, egv, &gid_map)?;
                } else {
                    debug!("Could not type expression {:?} while inferring generic fn call", exp);
                }
            }

            // step 3: optionally unify return type and update cgvs
            if let Some(rty) = rty {
                // XXX(unimpl) multi-return statements not supported
                self.fdef_gen_ty(&ret[0], rty, egv, &gid_map)?;
            }

            // step 4: if we've determined the explicit generic values, write them back to the call
            // otherwise return an error
            if egv.iter().any(|eg| matches!(eg, Underscore(_))) {
                return Err(ZVisitorError(format!(
                    "ZStatementWalker: failed to infer generics in fn call:\n{}\n\n{:?}\n{:?}",
                    span_to_string(&call.span),
                    egv,
                    gid_map,
                )));
            }
        }

        // rewrite return type and return it
        // XXX(perf) do this without so much cloning? probably changes ZExpressionRewriter
        let egv = call
            .explicit_generics
            .as_ref()
            .map(|eg| {
                {
                    eg.values.iter().map(|cgv| match cgv {
                        Underscore(_) => unreachable!(),
                        Value(l) => ast::Expression::Literal(l.clone()),
                        Identifier(i) => ast::Expression::Identifier(i.clone()),
                    })
                }
                .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let gvmap = fdef
            .generics
            .iter()
            .map(|ie| ie.value.clone())
            .zip(egv.into_iter())
            .collect::<HashMap<String, ast::Expression<'ast>>>();

        let mut ret_rewriter = ZExpressionRewriter::new(gvmap);
        let mut ret_ty = fdef.returns.first().unwrap().clone();
        ret_rewriter.visit_type(&mut ret_ty).map(|_| ret_ty)
        */

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
            // XXX(todo) handle EMBED/* functions
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
                    let rty = if alen == 1 {
                        rty
                    } else {
                        None
                    };
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
        eq_type(&ty, &acc_ty)
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
        let u32_ty = Basic(ast::BasicType::U32(ast::U32Type {
            span: ai.span.clone(),
        }));
        self.unify_expression(u32_ty, &mut *ai.count)?;

        let arr_ty = if at.dimensions.len() > 1 {
            at.dimensions.remove(0); // perf?
            Array(at)
        } else {
            bos_to_type(at.ty)
        };
        self.unify_expression(arr_ty, &mut *ai.value)
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

        let mut sm_types = self.monomorphize_struct(&st)?
            .fields
            .into_iter()
            .map(|sf| (sf.id.value, sf.ty))
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
                span: at.span.clone(),
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
        ie: &mut ast::IdentifierExpression<'ast>,
    ) -> ZVisitorResult {
        self.lookup_type(ie).and_then(|ity| eq_type(&ty, &ity))
    }

    fn unify_ternary(
        &self,
        ty: ast::Type<'ast>,
        te: &mut ast::TernaryExpression<'ast>,
    ) -> ZVisitorResult {
        // first expr must have type Bool, others the expected output type
        let bool_ty = ast::Type::Basic(ast::BasicType::Boolean(ast::BooleanType {
            span: te.span.clone(),
        }));
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
            BitXor | BitAnd | BitOr | Rem => match &bt {
                U8(_) | U16(_) | U32(_) | U64(_) => Ok((Basic(bt.clone()), Basic(bt))),
                _ => Err(ZVisitorError(
                    "ZStatementWalker: Bit/Rem operators require U* operands".to_owned(),
                )),
            },
            RightShift | LeftShift => match &bt {
                U8(_) | U16(_) | U32(_) | U64(_) => Ok((
                    Basic(bt),
                    Basic(U32(ast::U32Type {
                        span: be.span.clone(),
                    })),
                )),
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
            Add | Sub | Mul | Div => match &bt {
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
                            eq_type(&lty, &rty)
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
                Field(_) => Ok((
                    Basic(bt),
                    Basic(U32(ast::U32Type {
                        span: be.span.clone(),
                    })),
                )),
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
                        Field(_) => Ok(DS::Field(ast::FieldSuffix {
                            span: dle.span.clone(),
                        })),
                        U8(_) => Ok(DS::U8(ast::U8Suffix {
                            span: dle.span.clone(),
                        })),
                        U16(_) => Ok(DS::U16(ast::U16Suffix {
                            span: dle.span.clone(),
                        })),
                        U32(_) => Ok(DS::U32(ast::U32Suffix {
                            span: dle.span.clone(),
                        })),
                        U64(_) => Ok(DS::U64(ast::U64Suffix {
                            span: dle.span.clone(),
                        })),
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
                        self.monomorphize_struct(&sty)?
                            .fields
                            .iter()
                            .find(|f| &f.id.value == &macc.id.value)
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
            .ok_or_else(|| ZVisitorError(format!("ZStatementWalker: undeclared function {}", id)))
    }

    fn get_struct(&self, id: &str) -> ZResult<&ast::StructDefinition<'ast>> {
        self.zgen.get_struct(id).ok_or_else(|| {
            ZVisitorError(format!("ZStatementWalker: undeclared struct type {}", id))
        })
    }

    fn const_defined(&self, id: &str) -> bool {
        self.zgen.const_defined(id)
    }

    fn generic_defined(&self, id: &str) -> bool {
        // XXX(perf) if self.gens is long this could be improved with a HashSet.
        // Realistically, a function will have a small number of generic params.
        self.gens.iter().any(|g| &g.value == id)
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
                span: id.span.clone(),
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
                "ZStatementWalker: attempted to shadow generic {}",
                nm,
            )))
        } else if self.const_defined(nm) {
            Err(ZVisitorError(format!(
                "ZStatementWalker: attempted to shadow const {}",
                nm,
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

    fn monomorphize_struct(&self, sty: &ast::StructType<'ast>) -> ZResult<ast::StructDefinition<'ast>> {
        let mut sdef = self.get_struct(&sty.id.value)?.clone();
        // short circuit for non-generic structs
        if sdef.generics.is_empty() {
            return if sty.explicit_generics.is_some() {
                Err(ZVisitorError(format!(
                    "ZStatementWalker: got explicit generics for non-generic struct type {}:\n{}",
                    &sty.id.value,
                    span_to_string(&sty.span),
                )))
            } else {
                Ok(sdef)
            };
        }

        if sty.explicit_generics.is_none() {
            return Err(ZVisitorError(format!(
                "ZStatementWalker: no explicit generics found monomorphizing struct {}",
                &sty.id.value,

            )));
        }

        // XXX(q) rewrite id field of sdef?
        let generics = std::mem::take(&mut sdef.generics);
        let gen_values = &sty.explicit_generics.as_ref().unwrap().values;
        assert_eq!(generics.len(), gen_values.len());

        use ast::ConstantGenericValue::*;
        let gvmap = generics
            .into_iter()
            .map(|ie| ie.value)
            .zip(gen_values.iter().map(|cgv| match cgv {
                Underscore(_) => unreachable!(),
                Value(l) => ast::Expression::Literal(l.clone()),
                Identifier(i) => ast::Expression::Identifier(i.clone()),
            }))
            .collect::<HashMap<String, ast::Expression<'ast>>>();

        // rewrite struct definition
        let mut sf_rewriter = ZExpressionRewriter::new(gvmap);
        sdef.fields
            .iter_mut()
            .try_for_each(|f| sf_rewriter.visit_struct_field(f))?;

        Ok(sdef)
    }

    fn monomorphic_struct(&self, sty: &mut ast::StructType<'ast>) -> ZResult<ast::Type<'ast>> {
        use ast::ConstantGenericValue as CGV;

        // get the struct definition and return early if we don't have to handle generics
        let sdef = self.get_struct(&sty.id.value)?;
        if sdef.generics.is_empty() {
            return if sty.explicit_generics.is_some() {
                Err(ZVisitorError(format!(
                    "ZStatementWalker: got explicit generics for non-generic struct type {}:\n{}",
                    &sty.id.value,
                    span_to_string(&sty.span),
                )))
            } else {
                Ok(ast::Type::Struct(sty.clone()))
            };
        }

        // check explicit generics
        let mut eg = sty
            .explicit_generics
            .take()
            .ok_or_else(|| {
                ZVisitorError(format!(
                    "ZStatementWalker: must declare explicit generics for type {} in LHS:\n{}",
                    &sty.id.value,
                    span_to_string(&sty.span),
                ))
            })
            .and_then(|eg| {
                if eg.values.len() != sdef.generics.len() {
                    Err(ZVisitorError(format!(
                        "ZStatementWalker: wrong number of explicit generics for struct {}:\n{}",
                        &sty.id.value,
                        span_to_string(&sty.span),
                    )))
                } else if eg.values.iter().any(|v| matches!(v, CGV::Underscore(_))) {
                    Err(ZVisitorError(format!(
                        "ZStatementWalker: must specify all generic arguments for LHS struct {}:\n{}",
                        &sty.id.value,
                        span_to_string(&sty.span),
                    )))
                } else {
                    // make sure identifiers are actually defined!
                    eg.values.iter().try_for_each(|v|
                        if let CGV::Identifier(ie) = v {
                            if self.const_defined(&ie.value) || self.generic_defined(&ie.value) {
                                Ok(())
                            } else {
                                Err(ZVisitorError(format!(
                                    "ZStatementWalker: {} undef or non-const in {} generics:\n{}",
                                    &ie.value,
                                    &sty.id.value,
                                    span_to_string(&sty.span),
                                )))
                            }
                        } else {
                            Ok(())
                        }
                    ).map(|_| eg)
                }
            })?;

        // rewrite untyped literals
        let mut rewriter = ZConstLiteralRewriter::new(None);
        eg.values.iter_mut()
            .try_for_each(|cgv| rewriter.visit_constant_generic_value(cgv))?;

        // put gen_values back
        sty.explicit_generics = Some(eg);

        Ok(ast::Type::Struct(sty.clone()))
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
            span: asrt.span.clone(),
        }));
        self.unify(Some(bool_ty), &mut asrt.expression)?;
        walk_assertion_statement(self, asrt)
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

    fn visit_assignee(
        &mut self,
        asgn: &mut ast::Assignee<'ast>,
    ) -> ZVisitorResult {
        if !self.var_defined(&asgn.id.value) {
            Err(ZVisitorError(format!(
                "ZStatementWalker: assignment to undeclared variable {}",
                &asgn.id.value
            )))
        } else {
            walk_assignee(self, asgn)
        }
    }

    fn visit_typed_identifier(
        &mut self,
        ti: &mut ast::TypedIdentifier<'ast>,
    ) -> ZVisitorResult {
        ZConstLiteralRewriter::new(None).visit_type(&mut ti.ty)?;
        let ty = if let ast::Type::Struct(sty) = &mut ti.ty {
            self.monomorphic_struct(sty)?
        } else {
            ti.ty.clone()
        };
        self.insert_var(&ti.identifier.value, ty)?;
        walk_typed_identifier(self, ti)
    }

    fn visit_range_or_expression(
        &mut self,
        roe: &mut ast::RangeOrExpression<'ast>,
    ) -> ZVisitorResult {
        use ast::RangeOrExpression::*;
        match roe {
            Range(r) => self.visit_range(r),
            Expression(e) => {
                let mut zty = ZExpressionTyper::new(self);
                if self.type_expression(e, &mut zty)?.is_none() {
                    let mut zrw = ZConstLiteralRewriter::new(Some(Ty::Uint(32)));
                    zrw.visit_expression(e)?;
                }
                self.visit_expression(e)
            }
        }
    }

    fn visit_range(
        &mut self,
        rng: &mut ast::Range<'ast>,
    ) -> ZVisitorResult {
        let mut zty = ZExpressionTyper::new(self);
        let fty = rng.from.as_mut()
            .map(|fexp| self.type_expression(&mut fexp.0, &mut zty)).transpose()?.flatten();
        let tty = rng.to.as_mut()
            .map(|texp| self.type_expression(&mut texp.0, &mut zty)).transpose()?.flatten();
        match (fty, tty) {
            (None, None) => {
                let mut zrw = ZConstLiteralRewriter::new(Some(Ty::Uint(32)));
                rng.from.as_mut().map(|fexp| zrw.visit_expression(&mut fexp.0)).transpose()?;
                rng.to.as_mut().map(|texp| zrw.visit_expression(&mut texp.0)).transpose()?;
                Ok(())
            }
            (Some(fty), None) => rng.to.as_mut().map(|texp| self.unify_expression(fty, &mut texp.0)).unwrap_or(Ok(())),
            (None, Some(tty)) => rng.from.as_mut().map(|fexp| self.unify_expression(tty, &mut fexp.0)).unwrap_or(Ok(())),
            (Some(fty), Some(tty)) => eq_type(&fty, &tty)
                .map_err(|e| ZVisitorError(format!(
                    "typing Range: {}\n{}",
                    e.0,
                    span_to_string(&rng.span),
                ))),
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
