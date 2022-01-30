//! Generic parameter inference


use crate::ir::term::{bv_lit, leaf_term, term, BoolNaryOp, Op, Sort, Term, Value};
use crate::target::smt::find_unique_model;
use super::super::{ZGen, span_to_string};
use super::super::term::{Ty, T, cond};

use rand::{distributions::Alphanumeric, Rng};
use std::collections::HashMap;
use zokrates_pest_ast as ast;

pub(in super::super) struct ZGenericInf<'ast, 'gen> {
    zgen: &'gen ZGen<'ast>,
    fdef: &'gen ast::FunctionDefinition<'ast>,
    gens: &'gen [ast::IdentifierExpression<'ast>],
    sfx: String,
    constr: Option<Term>,
}

impl<'ast, 'gen> ZGenericInf<'ast, 'gen> {
    pub fn new(zgen: &'gen ZGen<'ast>, fdef: &'gen ast::FunctionDefinition<'ast>) -> Self {
        let gens = fdef.generics.as_ref();
        let sfx = make_sfx(
            (&mut rand::thread_rng())
                .sample_iter(Alphanumeric)
                .map(char::from)
                .take(8)
                .collect(),
            &fdef.id.value,
        );
        Self {
            zgen,
            fdef,
            gens,
            sfx,
            constr: None,
        }
    }

    fn is_generic_var(&self, var: &str) -> bool {
        self.gens.iter().any(|id| &id.value == var)
    }

    fn add_constraint(&mut self, lhs: Term, rhs: Term) {
        let new_term = term![Op::Eq; lhs, rhs];
        let new_term = if let Some(old_term) = self.constr.take() {
            term![Op::BoolNaryOp(BoolNaryOp::And); old_term, new_term]
        } else {
            new_term
        };
        self.constr = Some(new_term);
    }
    
    pub fn unify_generic(
        &mut self,
        call: &ast::CallAccess<'ast>,
        rty: Option<Ty>,
        args: &[T],
    ) -> Result<HashMap<String, T>, String> {
        use ast::ConstantGenericValue as CGV;
        // start from an empty constraint
        self.constr = None;
        self.gens = &self.fdef.generics[..];
        if self.gens.is_empty() {
            return Ok(HashMap::new());
        }

        // 1. build up the already-known generics
        if let Some(eg) = call.explicit_generics.as_ref() {
            for (cgv, id) in eg.values.iter().zip(self.fdef.generics.iter()) {
                if let Some(v) = match cgv {
                    CGV::Underscore(_) => None,
                    CGV::Value(v) => Some(self.zgen.literal_(v)),
                    CGV::Identifier(i) => Some(self.zgen.const_identifier_(i)),
                } {
                    let var = make_varname(&id.value, &self.sfx);
                    let val = match v? {
                        T::Uint(32, val) => Ok(val),
                        v => Err(format!("ZGenericInf: ConstantGenericValue for {} had type {}, expected u32", &id.value, v.type_())),
                    }?;
                    self.add_constraint(var, val);
                }
            }
        }

        // 2. for each argument, update the const generic values
        for (pty, arg) in self.fdef.parameters.iter().map(|p| &p.ty).zip(args.iter()) {
            let aty = arg.type_();
            self.fdef_gen_ty(aty, pty)?;
        }
        // bracketing invariant
        assert!(self.gens == &self.fdef.generics[..]);
        assert!(self.sfx.ends_with(&self.fdef.id.value));

        // 3. unify the return type
        match (rty, self.fdef.returns.first()) {
            (Some(rty), Some(ret)) => self.fdef_gen_ty(rty, ret)?,
            (Some(rty), None) if rty != Ty::Bool => Err(format!("Function {} expected implicit Bool ret, but got {}", &self.fdef.id.value, rty))?,
            (Some(_), None) => (),
            (None, _) => (),
        }
        // bracketing invariant
        assert!(self.gens == &self.fdef.generics[..]);
        assert!(self.sfx.ends_with(&self.fdef.id.value));

        // 4. run the solver on the term stack
        let g_names = self.gens.iter().map(|gid| make_varname_str(&gid.value, &self.sfx)).collect::<Vec<_>>();
        let mut solved = self.constr.as_ref()
            .and_then(|t| find_unique_model(t, g_names.clone()))
            .unwrap_or_else(|| HashMap::new());

        // 5. extract the assignments from the solver result
        let mut res = HashMap::new();
        assert_eq!(g_names.len(), self.gens.len());
        g_names.into_iter().enumerate().for_each(|(idx, mut g_name)| {
            if let Some(g_val) = solved.remove(&g_name) {
                match &g_val {
                    Value::BitVector(bv) => assert!(bv.width() == 32),
                    _ => unreachable!(),
                }
                g_name.truncate(self.gens[idx].value.len());
                g_name.shrink_to_fit();
                assert!(res.insert(g_name, T::Uint(32, term![Op::Const(g_val)])).is_none());
            }
        });
        Ok(res)
    }

    fn fdef_gen_ty(
        &mut self,
        arg_ty: Ty,
        def_ty: &ast::Type<'ast>,
    ) -> Result<(), String> {
        use ast::Type as TT;
        match def_ty {
            TT::Basic(dty_b) => self.fdef_gen_ty_basic(arg_ty, dty_b),
            TT::Array(dty_a) => self.fdef_gen_ty_array(arg_ty, dty_a),
            TT::Struct(dty_s) => self.fdef_gen_ty_struct(arg_ty, dty_s),
        }
    }

    fn fdef_gen_ty_basic(
        &self,
        arg_ty: Ty,
        bas_ty: &ast::BasicType<'ast>,
    ) -> Result<(), String> {
        // XXX(q) dispatch to const_ or not? does not seem necessary because arg is Type::Basic
        if arg_ty != self.zgen.const_type_(&ast::Type::Basic(bas_ty.clone())) {
            Err(format!("Type mismatch unifying generics: got {}, decl was {:?}", arg_ty, bas_ty))
        } else {
            Ok(())
        }
    }

    fn fdef_gen_ty_array(
        &mut self,
        mut arg_ty: Ty,
        def_ty: &ast::ArrayType<'ast>,
    ) -> Result<(), String> {
        if !matches!(arg_ty, Ty::Array(_, _)) {
            Err(format!("Type mismatch unifying generics: got {}, decl was Array", arg_ty))?;
        }

        // iterate through array dimensions, unifying each with fn decl
        let mut dim_off = 0;
        loop {
            match arg_ty {
                Ty::Array(arg_dim, nty) => {
                    // make sure that we expect at least one more array dim
                    if dim_off >= def_ty.dimensions.len() {
                        Err(format!(
                            "Type mismatch: got >={}-dim array, decl was {} dims",
                            dim_off,
                            def_ty.dimensions.len(),
                        ))?;
                    }

                    // unify actual dimension with dim expression
                    self.fdef_gen_ty_expr(arg_dim, &def_ty.dimensions[dim_off])?;

                    // iterate
                    dim_off += 1;
                    arg_ty = *nty;
                }
                nty => {
                    // make sure we didn't expect any more array dims!
                    if dim_off != def_ty.dimensions.len() {
                        Err(format!(
                            "Type mismatch: got {}-dim array, decl had {} dims",
                            dim_off,
                            def_ty.dimensions.len(),
                        ))?;
                    }

                    arg_ty = nty;
                    break;
                }
            };
        }

        use ast::BasicOrStructType as BoST;
        match &def_ty.ty {
            BoST::Struct(dty_s) => self.fdef_gen_ty_struct(arg_ty, dty_s),
            BoST::Basic(dty_b) => self.fdef_gen_ty_basic(arg_ty, dty_b),
        }
    }

    fn fdef_gen_ty_struct(
        &mut self,
        arg_ty: Ty,
        def_ty: &ast::StructType<'ast>,
    ) -> Result<(), String> {
        // check type and struct name
        let mut aty_map = match arg_ty {
            Ty::Struct(aty_n, aty_map) if &aty_n == &def_ty.id.value => Ok(aty_map),
            Ty::Struct(aty_n, _) => Err(format!("Type mismatch: got struct {}, decl was struct {}", &aty_n, &def_ty.id.value)),
            arg_ty => Err(format!("Type mismatch unifying generics: got {}, decl was Struct", arg_ty)),
        }?;
        let strdef = self.zgen.get_struct(&def_ty.id.value)
            .ok_or_else(|| format!("ZGenericInf: no such struct {}", &def_ty.id.value))?;

        // short-circuit if there are no generics in this struct
        if strdef.generics.is_empty() {
            return if def_ty.explicit_generics.is_some() {
                Err(format!(
                    "Unifying generics: got explicit generics for non-generic struct type {}:\n{}",
                    &def_ty.id.value,
                    span_to_string(&def_ty.span),
                ))
            } else {
                Ok(())
            }
        }

        // struct type in fn defn must provide explicit generics
        use ast::ConstantGenericValue as CGV;
        if def_ty.explicit_generics
            .as_ref()
            .map(|eg| eg.values.iter().any(|eg| matches!(eg, CGV::Underscore(_))))
            .unwrap_or(true)
        {
            Err(format!(
                "Cannot infer generic values for struct {} arg to function {}\nGeneric structs in fn defns must have explicit generics (in terms of fn generic vars)",
                &def_ty.id.value,
                &self.fdef.id.value,
            ))?;
        }

        // 1. set up mapping from outer explicit generics to inner explicit generics
        let new_sfx = make_sfx(self.sfx.clone(), &def_ty.id.value);
        def_ty.explicit_generics.as_ref().unwrap().values.iter()
            .zip(strdef.generics.iter())
            .try_for_each::<_,Result<(),String>>(|(cgv, id)| {
                let sgid = make_varname(&id.value, &new_sfx);
                let val = match cgv {
                    CGV::Underscore(_) => unreachable!(),
                    CGV::Value(le) => {
                        u32_term(self.zgen.literal_(le)?)?
                    }
                    CGV::Identifier(id) => {
                        if self.is_generic_var(&id.value) {
                            make_varname(&id.value, &self.sfx)
                        } else {
                            u32_term(self.zgen.const_identifier_(&id)?)?
                        }
                    }
                };
                self.add_constraint(sgid, val);
                Ok(())
            })?;

        // 2. walk through struct def to generate constraints on inner explicit generics
        let old_sfx = std::mem::replace(&mut self.sfx, new_sfx);
        let old_gens = std::mem::replace(&mut self.gens, &strdef.generics[..]);
        for ast::StructField { ty, id, .. } in strdef.fields.iter() {
            if let Some(t) = aty_map.remove(&id.value) {
                self.fdef_gen_ty(t, ty)?;
            } else {
                Err(format!("ZGenericInf: missing member {} in struct {} value",
                    &id.value,
                    &def_ty.id.value,
                ))?;
            }
        }
        if !aty_map.is_empty() {
            Err(format!("ZGenericInf: struct {} value had extra members: {:?}",
                &def_ty.id.value,
                aty_map.keys().collect::<Vec<_>>(),
            ))?;
        }

        // 3. pop stack and continue
        self.gens = old_gens;
        self.sfx = old_sfx;
        Ok(())
    }

    // turn an expr into a set of terms and assert equality
    fn fdef_gen_ty_expr(
        &mut self,
        arg_dim: usize,
        def_exp: &ast::Expression<'ast>,
    ) -> Result<(), String> {
        let t = u32_term(self.expr(def_exp)?)?;
        self.add_constraint(bv_lit(arg_dim, 32), t);
        Ok(())
    }

    fn expr(
        &self,
        expr: &ast::Expression<'ast>,
    ) -> Result<T, String> {
        use ast::Expression::*;
        match expr {
            Ternary(te) => {
                let cnd = self.expr(&te.first)?;
                let csq = self.expr(&te.second)?;
                let alt = self.expr(&te.third)?;
                cond(cnd, csq, alt)
            }
            Binary(be) => {
                let lhs = self.expr(&be.left)?;
                let rhs = self.expr(&be.right)?;
                let op = self.zgen.bin_op(&be.op);
                op(lhs, rhs)
            }
            Unary(ue) => {
                let exp = self.expr(&ue.expression)?;
                let op = self.zgen.unary_op(&ue.op);
                op(exp)
            }
            Identifier(id) => {
                if self.is_generic_var(&id.value) {
                    Ok(T::Uint(32, make_varname(&id.value, &self.sfx)))
                } else {
                    self.zgen.const_identifier_(&id)
                }
            }
            Literal(le) => self.zgen.literal_(le),
            Postfix(_) => Err("ZGenericInf: got Postfix in array dim expr (unimpl)".into()),
            InlineArray(_) => Err("ZGenericInf: got InlineArray in array dim expr (unimpl)".into()),
            InlineStruct(_) => Err("ZGenericInf: got InlineStruct in array dim expr (unimpl)".into()),
            ArrayInitializer(_) => Err("ZGenericInf: got ArrayInitializer in array dim expr (unimpl)".into()),
        }
    }
}

fn u32_term(t: T) -> Result<Term, String> {
    match t {
        T::Uint(32, t) => Ok(t),
        e => Err(format!("ZGenericInf: got {} for expr, expected T::Uint(32)", e.type_())),
    }
}

fn make_sfx(mut base: String, sfx: &str) -> String {
    base.push('_');
    base.push_str(sfx);
    base
}

fn make_varname_str(id: &str, sfx: &str) -> String {
    let mut tmp = String::from(id);
    tmp.push('_');
    tmp.push_str(sfx);
    tmp
}

fn make_varname(id: &str, sfx: &str) -> Term {
    let tmp = make_varname_str(id, sfx);
    term![Op::Var(tmp, Sort::BitVector(32))]
}
