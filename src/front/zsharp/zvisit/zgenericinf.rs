//! Generic parameter inference

use super::super::term::{cond, const_val, Ty, T};
use super::super::{span_to_string, ZGen};
use crate::ir::term::{bv_lit, leaf_term, term, BoolNaryOp, Op, Sort, Term, Value};
#[cfg(feature = "smt")]
use crate::target::smt::find_unique_model;

use log::debug;
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::Path;
use zokrates_pest_ast as ast;

thread_local! {
    static CACHE: RefCell<HashMap<Term, HashMap<String, T>>> = RefCell::new(HashMap::new());
}

pub(in super::super) struct ZGenericInf<'ast, 'gen, const IS_CNST: bool> {
    zgen: &'gen ZGen<'ast>,
    fdef: &'gen ast::FunctionDefinition<'ast>,
    gens: &'gen [ast::IdentifierExpression<'ast>],
    path: &'gen Path,
    sfx: String,
    constr: Option<Term>,
}

impl<'ast, 'gen, const IS_CNST: bool> ZGenericInf<'ast, 'gen, IS_CNST> {
    pub fn new(
        zgen: &'gen ZGen<'ast>,
        fdef: &'gen ast::FunctionDefinition<'ast>,
        path: &'gen Path,
        name: &str,
    ) -> Self {
        let gens = fdef.generics.as_ref();
        let mut path_str = "___".to_string();
        path_str.push_str(&path.to_string_lossy());
        path_str.push_str("___");
        path_str.push_str(name);
        path_str.push_str("___");
        path_str.push_str(&fdef.id.value);
        let sfx = make_sfx(path_str, &fdef.id.value);
        Self {
            zgen,
            fdef,
            gens,
            path,
            sfx,
            constr: None,
        }
    }

    fn is_generic_var(&self, var: &str) -> bool {
        self.gens.iter().any(|id| id.value == var)
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

    fn const_id_(&self, id: &ast::IdentifierExpression<'ast>) -> Result<T, String> {
        self.zgen
            .identifier_impl_::<IS_CNST>(id)
            .and_then(const_val)
    }

    pub fn unify_generic<ATIter: Iterator<Item = Ty>>(
        &mut self,
        egv: &[ast::ConstantGenericValue<'ast>],
        rty: Option<Ty>,
        arg_tys: ATIter,
    ) -> Result<HashMap<String, T>, String> {
        debug!("ZGenericInf::unify_generic");
        use ast::ConstantGenericValue as CGV;
        self.constr = None;
        self.gens = &self.fdef.generics[..];

        // early returns: monomorphized or not generic
        if self.gens.is_empty() {
            debug!("done (no generics)");
            return Ok(HashMap::new());
        }
        if egv.len() == self.gens.len() && !egv.iter().any(|cgv| matches!(cgv, CGV::Underscore(_)))
        {
            match self
                .zgen
                .egvs_impl_::<IS_CNST>(egv, self.fdef.generics.clone())
            {
                Ok(gens) if gens.len() == self.gens.len() => {
                    debug!("done (explicit generics)");
                    return Ok(gens);
                }
                _ => (),
            };
        }

        // self.fdef is in the context of self.path
        self.zgen.file_stack_push(self.path.to_path_buf());

        // 1. build up the already-known generics
        for (cgv, id) in egv.iter().zip(self.fdef.generics.iter()) {
            if let Some(v) = match cgv {
                CGV::Underscore(_) => None,
                CGV::Value(v) => Some(self.zgen.literal_(v)?),
                CGV::Identifier(i) => Some(self.const_id_(i)?),
            } {
                let var = make_varname(&id.value, &self.sfx);
                let val = match v.ty {
                    Ty::Uint(32) => Ok(v.term),
                    ty => Err(format!(
                        "ZGenericInf: ConstantGenericValue for {} had type {}, expected u32",
                        &id.value, ty
                    )),
                }?;
                self.add_constraint(var, val);
            }
        }

        // 2. for each argument, update the const generic values
        for (pty, arg_ty) in self.fdef.parameters.iter().map(|p| &p.ty).zip(arg_tys) {
            self.fdef_gen_ty(arg_ty, pty)?;
            // bracketing invariant
            assert!(self.gens == &self.fdef.generics[..]);
            assert!(self.sfx.ends_with(&self.fdef.id.value));
        }

        // 3. unify the return type
        match (rty, self.fdef.returns.first()) {
            (Some(rty), Some(ret)) => self.fdef_gen_ty(rty, ret),
            (Some(rty), None) if rty != Ty::Bool => Err(format!(
                "Function {} expected implicit Bool ret, but got {}",
                &self.fdef.id.value, rty
            )),
            (Some(_), None) => Ok(()),
            (None, _) => Ok(()),
        }?;
        // bracketing invariant
        assert!(self.gens == &self.fdef.generics[..]);
        assert!(self.sfx.ends_with(&self.fdef.id.value));

        // back to calling context
        self.zgen.file_stack_pop();

        // 4. run the solver on the term stack, if it's not already cached
        if let Some(res) = self
            .constr
            .as_ref()
            .and_then(|t| CACHE.with(|c| c.borrow().get(t).cloned()))
        {
            assert!(self.gens.len() == res.len());
            assert!(self.gens.iter().all(|g| res.contains_key(&g.value)));
            debug!("done (cached result for {})", &self.sfx);
            return Ok(res);
        }
        let g_names = self
            .gens
            .iter()
            .map(|gid| make_varname_str(&gid.value, &self.sfx))
            .collect::<Vec<_>>();
        let mut solved = self
            .constr
            .as_ref()
            .and_then(|t| find_unique_model(t, g_names.clone()))
            .unwrap_or_default();

        // 5. extract the assignments from the solver result
        let mut res = HashMap::with_capacity(g_names.len());
        assert_eq!(g_names.len(), self.gens.len());
        g_names
            .into_iter()
            .enumerate()
            .for_each(|(idx, mut g_name)| {
                if let Some(g_val) = solved.remove(&g_name) {
                    match &g_val {
                        Value::BitVector(bv) => assert!(bv.width() == 32),
                        _ => unreachable!(),
                    }
                    g_name.truncate(self.gens[idx].value.len());
                    g_name.shrink_to_fit();
                    assert!(res
                        .insert(g_name, T::new(Ty::Uint(32), term![Op::Const(g_val)]))
                        .is_none());
                }
            });
        if self.constr.is_some() {
            CACHE.with(|c| {
                c.borrow_mut()
                    .insert(self.constr.take().unwrap(), res.clone())
            });
        }
        debug!("done (finished inference)");
        Ok(res)
    }

    fn fdef_gen_ty(&mut self, arg_ty: Ty, def_ty: &ast::Type<'ast>) -> Result<(), String> {
        use ast::Type as TT;
        match def_ty {
            TT::Basic(dty_b) => self.fdef_gen_ty_basic(arg_ty, dty_b),
            TT::Array(dty_a) => self.fdef_gen_ty_array(arg_ty, dty_a),
            TT::Struct(dty_s) => self.fdef_gen_ty_struct_or_type(arg_ty, dty_s),
        }
    }

    fn fdef_gen_ty_basic(&self, arg_ty: Ty, bas_ty: &ast::BasicType<'ast>) -> Result<(), String> {
        // XXX(q) dispatch to const_ or not? does not seem necessary because arg is Type::Basic
        if arg_ty
            != self
                .zgen
                .type_impl_::<IS_CNST>(&ast::Type::Basic(bas_ty.clone()))?
        {
            Err(format!(
                "Type mismatch unifying generics: got {arg_ty}, decl was {bas_ty:?}"
            ))
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
            return Err(format!(
                "Type mismatch unifying generics: got {arg_ty}, decl was Array",
            ));
        }

        // iterate through array dimensions, unifying each with fn decl
        let mut dim_off = 0;
        loop {
            match arg_ty {
                Ty::Array(arg_dim, nty) => {
                    // make sure that we expect at least one more array dim
                    if dim_off >= def_ty.dimensions.len() {
                        return Err(format!(
                            "Type mismatch: got >={}-dim array, decl was {} dims",
                            dim_off,
                            def_ty.dimensions.len(),
                        ));
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
                        return Err(format!(
                            "Type mismatch: got {}-dim array, decl had {} dims",
                            dim_off,
                            def_ty.dimensions.len(),
                        ));
                    }

                    arg_ty = nty;
                    break;
                }
            };
        }

        use ast::BasicOrStructType as BoST;
        match &def_ty.ty {
            BoST::Struct(dty_s) => self.fdef_gen_ty_struct_or_type(arg_ty, dty_s),
            BoST::Basic(dty_b) => self.fdef_gen_ty_basic(arg_ty, dty_b),
        }
    }

    fn fdef_gen_ty_struct_or_type(
        &mut self,
        arg_ty: Ty,
        def_ty: &ast::StructType<'ast>,
    ) -> Result<(), String> {
        let (stdef, stpath) = self
            .zgen
            .get_struct_or_type(&def_ty.id.value)
            .ok_or_else(|| format!("ZGenericInf: no struct struct or type {}", &def_ty.id.value))?;
        let generics = match &stdef {
            Ok(strdef) => &strdef.generics[..],
            Err(tydef) => &tydef.generics[..],
        };

        // short-circuit if there are no generics in this struct
        if generics.is_empty() {
            return if def_ty.explicit_generics.is_some() {
                Err(format!(
                    "Unifying generics: got explicit generics for non-generic struct type {}:\n{}",
                    &def_ty.id.value,
                    span_to_string(&def_ty.span),
                ))
            } else {
                Ok(())
            };
        }

        // struct type in fn defn must provide explicit generics
        use ast::ConstantGenericValue as CGV;
        if def_ty
            .explicit_generics
            .as_ref()
            .map(|eg| eg.values.iter().any(|eg| matches!(eg, CGV::Underscore(_))))
            .unwrap_or(true)
        {
            return Err(format!(
                "Cannot infer generic values for struct {} arg to function {}\nGeneric structs in fn defns must have explicit generics (in terms of fn generic vars)",
                &def_ty.id.value,
                &self.fdef.id.value,
            ));
        }

        // 1. set up mapping from outer explicit generics to inner explicit generics
        let new_sfx = make_sfx(self.sfx.clone(), &def_ty.id.value);
        def_ty
            .explicit_generics
            .as_ref()
            .unwrap()
            .values
            .iter()
            .zip(generics.iter())
            .try_for_each::<_, Result<(), String>>(|(cgv, id)| {
                let sgid = make_varname(&id.value, &new_sfx);
                let val = match cgv {
                    CGV::Underscore(_) => unreachable!(),
                    CGV::Value(le) => u32_term(self.zgen.literal_(le)?)?,
                    CGV::Identifier(id) => {
                        if self.is_generic_var(&id.value) {
                            make_varname(&id.value, &self.sfx)
                        } else {
                            u32_term(self.const_id_(id)?)?
                        }
                    }
                };
                self.add_constraint(sgid, val);
                Ok(())
            })?;

        // 2. walk through struct def to generate constraints on inner explicit generics
        let old_sfx = std::mem::replace(&mut self.sfx, new_sfx);
        let old_gens = std::mem::replace(&mut self.gens, generics);
        self.zgen.file_stack_push(stpath);
        match stdef {
            Ok(strdef) => {
                // check type and struct name
                let mut aty_map = match arg_ty {
                    Ty::Struct(aty_n, aty_map) if aty_n == def_ty.id.value => {
                        Ok(aty_map.into_map())
                    }
                    Ty::Struct(aty_n, _) => Err(format!(
                        "Type mismatch: got struct {aty_n}, decl was struct {}",
                        &def_ty.id.value
                    )),
                    arg_ty => Err(format!(
                        "Type mismatch unifying generics: got {arg_ty}, decl was Struct",
                    )),
                }?;
                for ast::StructField { ty, id, .. } in strdef.fields.iter() {
                    if let Some(t) = aty_map.remove(&id.value) {
                        self.fdef_gen_ty(t, ty)?;
                    } else {
                        return Err(format!(
                            "ZGenericInf: missing member {} in struct {} value",
                            &id.value, &def_ty.id.value,
                        ));
                    }
                }
                if !aty_map.is_empty() {
                    return Err(format!(
                        "ZGenericInf: struct {} value had extra members: {:?}",
                        &def_ty.id.value,
                        aty_map.keys().collect::<Vec<_>>(),
                    ));
                }
            }
            Err(tydef) => {
                self.fdef_gen_ty(arg_ty, &tydef.ty)?;
            }
        }

        // 3. pop stack and continue
        self.zgen.file_stack_pop();
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

    fn expr(&self, expr: &ast::Expression<'ast>) -> Result<T, String> {
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
                    Ok(T::new(Ty::Uint(32), make_varname(&id.value, &self.sfx)))
                } else {
                    self.const_id_(id)
                }
            }
            Literal(le) => self.zgen.literal_(le),
            Postfix(_) => Err("ZGenericInf: got Postfix in array dim expr (unimpl)".into()),
            InlineArray(_) => Err("ZGenericInf: got InlineArray in array dim expr (unimpl)".into()),
            InlineStruct(_) => {
                Err("ZGenericInf: got InlineStruct in array dim expr (unimpl)".into())
            }
            ArrayInitializer(_) => {
                Err("ZGenericInf: got ArrayInitializer in array dim expr (unimpl)".into())
            }
        }
    }
}

fn u32_term(t: T) -> Result<Term, String> {
    match t.ty {
        Ty::Uint(32) => Ok(t.term),
        ty => Err(format!(
            "ZGenericInf: got {ty} for expr, expected T::Uint(32)"
        )),
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
