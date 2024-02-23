//! Type(Sort)-checking

use super::*;

use std::cell::RefCell;

use circ_hc::collections::cache::NodeCache;

thread_local! {
    pub(super) static TERM_TYPES: RefCell<TypeTable> = RefCell::new(NodeCache::new());
}

#[track_caller]
/// Type-check this term, at a surface level.
/// That is, determine its type without a full validity check.
pub fn check(t: &Term) -> Sort {
    check_raw(t).unwrap()
}

#[track_caller]
/// Fully type-check this term.
/// That is, determine its type *with* a full validity check.
pub fn check_rec(t: &Term) -> Sort {
    rec_check_raw(t).unwrap()
}

/// Return a list of child terms that must be typed first to type this term.
fn check_dependencies(t: &Term) -> Vec<Term> {
    match &t.op() {
        Op::Ite => vec![t.cs()[1].clone()],
        Op::Eq => Vec::new(),
        Op::Var(_, _) => Vec::new(),
        Op::Const(_) => Vec::new(),
        Op::BvBinOp(_) => vec![t.cs()[0].clone()],
        Op::BvBinPred(_) => Vec::new(),
        Op::BvNaryOp(_) => vec![t.cs()[0].clone()],
        Op::BvUnOp(_) => vec![t.cs()[0].clone()],
        Op::BoolToBv => Vec::new(),
        Op::BvExtract(_, _) => Vec::new(),
        Op::BvConcat => t.cs().to_vec(),
        Op::BvUext(_) => vec![t.cs()[0].clone()],
        Op::BvSext(_) => vec![t.cs()[0].clone()],
        Op::PfToBv(_) => Vec::new(),
        Op::Implies => Vec::new(),
        Op::BoolNaryOp(_) => Vec::new(),
        Op::Not => Vec::new(),
        Op::BvBit(_) => Vec::new(),
        Op::BoolMaj => Vec::new(),
        Op::FpBinOp(_) => vec![t.cs()[0].clone()],
        Op::FpBinPred(_) => Vec::new(),
        Op::FpUnPred(_) => Vec::new(),
        Op::FpUnOp(_) => vec![t.cs()[0].clone()],
        Op::BvToFp => vec![t.cs()[0].clone()],
        Op::UbvToFp(_) => Vec::new(),
        Op::SbvToFp(_) => Vec::new(),
        Op::FpToFp(_) => Vec::new(),
        Op::PfUnOp(_) => vec![t.cs()[0].clone()],
        Op::PfDiv => vec![t.cs()[0].clone()],
        Op::PfNaryOp(_) => vec![t.cs()[0].clone()],
        Op::IntNaryOp(_) => Vec::new(),
        Op::IntBinPred(_) => Vec::new(),
        Op::UbvToPf(_) => Vec::new(),
        Op::PfChallenge(_, _) => Vec::new(),
        Op::PfFitsInBits(_) => Vec::new(),
        Op::Select => vec![t.cs()[0].clone()],
        Op::Store => vec![t.cs()[0].clone()],
        Op::Array(..) => Vec::new(),
        Op::CStore => vec![t.cs()[0].clone()],
        Op::Fill(..) => vec![t.cs()[0].clone()],
        Op::Tuple => t.cs().to_vec(),
        Op::Field(_) => vec![t.cs()[0].clone()],
        Op::Update(_i) => vec![t.cs()[0].clone()],
        Op::Map(_) => t.cs().to_vec(),
        Op::Call(_, _, _) => Vec::new(),
        Op::Rot(_) => vec![t.cs()[0].clone()],
        Op::PfToBoolTrusted => Vec::new(),
        Op::ExtOp(o) => o.check_dependencies(t),
    }
}

fn check_raw_step(t: &Term, tys: &TypeTable) -> Result<Sort, TypeErrorReason> {
    let get_ty = |term: &Term| -> &Sort {
        tys.get(&term.downgrade()).unwrap_or_else(|| panic!("When checking the type of {} we needed the type of {}, but it was missing. This is a bug in check_dependencies", t, term))
    };
    match &t.op() {
        Op::Ite => Ok(get_ty(&t.cs()[1]).clone()),
        Op::Eq => Ok(Sort::Bool),
        Op::Var(_, s) => Ok(s.clone()),
        Op::Const(c) => Ok(c.sort()),
        Op::BvBinOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::BvBinPred(_) => Ok(Sort::Bool),
        Op::BvNaryOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::BvUnOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::BoolToBv => Ok(Sort::BitVector(1)),
        Op::BvExtract(a, b) => Ok(Sort::BitVector(a - b + 1)),
        Op::BvConcat => t
            .cs()
            .iter()
            .map(get_ty)
            .try_fold(0, |l: usize, r: &Sort| -> Result<usize, TypeErrorReason> {
                bv_or(r, "concat").map(|rr| l + rr.as_bv())
            })
            .map(Sort::BitVector),
        Op::BvUext(a) => {
            bv_or(get_ty(&t.cs()[0]), "bv-uext").map(|bv| Sort::BitVector(bv.as_bv() + a))
        }
        Op::BvSext(a) => {
            bv_or(get_ty(&t.cs()[0]), "bv-uext").map(|bv| Sort::BitVector(bv.as_bv() + a))
        }
        Op::PfToBv(a) => Ok(Sort::BitVector(*a)),
        Op::Implies => Ok(Sort::Bool),
        Op::BoolNaryOp(_) => Ok(Sort::Bool),
        Op::Not => Ok(Sort::Bool),
        Op::BvBit(_) => Ok(Sort::Bool),
        Op::BoolMaj => Ok(Sort::Bool),
        Op::FpBinOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::FpBinPred(_) => Ok(Sort::Bool),
        Op::FpUnPred(_) => Ok(Sort::Bool),
        Op::FpUnOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::BvToFp => match bv_or(get_ty(&t.cs()[0]), "bv-to-fp") {
            Ok(Sort::BitVector(32)) => Ok(Sort::F32),
            Ok(Sort::BitVector(64)) => Ok(Sort::F64),
            Ok(s) => Err(TypeErrorReason::Custom(format!(
                "Cannot convert {s} to floating-point"
            ))),
            Err(e) => Err(e),
        },
        Op::UbvToFp(64) => Ok(Sort::F64),
        Op::UbvToFp(32) => Ok(Sort::F32),
        Op::SbvToFp(64) => Ok(Sort::F64),
        Op::SbvToFp(32) => Ok(Sort::F32),
        Op::FpToFp(64) => Ok(Sort::F64),
        Op::FpToFp(32) => Ok(Sort::F32),
        Op::PfUnOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::PfDiv => Ok(get_ty(&t.cs()[0]).clone()),
        Op::PfNaryOp(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::IntNaryOp(_) => Ok(Sort::Int),
        Op::IntBinPred(_) => Ok(Sort::Bool),
        Op::UbvToPf(m) => Ok(Sort::Field(m.clone())),
        Op::PfChallenge(_, m) => Ok(Sort::Field(m.clone())),
        Op::PfFitsInBits(_) => Ok(Sort::Bool),
        Op::Select => array_or(get_ty(&t.cs()[0]), "select").map(|(_, v, _)| v.clone()),
        Op::Store => Ok(get_ty(&t.cs()[0]).clone()),
        Op::Array(k, v) => Ok(Sort::Array(
            Box::new(k.clone()),
            Box::new(v.clone()),
            t.cs().len(),
        )),
        Op::CStore => Ok(get_ty(&t.cs()[0]).clone()),
        Op::Fill(key_sort, size) => Ok(Sort::Array(
            Box::new(key_sort.clone()),
            Box::new(get_ty(&t.cs()[0]).clone()),
            *size,
        )),
        Op::Tuple => Ok(Sort::Tuple(t.cs().iter().map(get_ty).cloned().collect())),
        Op::Field(i) => {
            let sort = get_ty(&t.cs()[0]);
            let sorts = sort.as_tuple();
            if i < &sorts.len() {
                Ok(sorts[*i].clone())
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "index {i} in tuple of sort {sort}"
                )))
            }
        }
        Op::Update(_i) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::Map(op) => {
            let arg_cnt = t.cs().len();
            let mut arg_sorts_to_inner_op = Vec::new();

            let mut key_sort = Sort::Bool;
            let mut size = 0;
            let mut error = None;

            match arrmap_or(get_ty(&t.cs()[0]), "map") {
                Ok((k, _, s)) => {
                    key_sort = k.clone();
                    size = *s;
                }
                Err(e) => {
                    error = Some(e);
                }
            }

            for i in 0..arg_cnt {
                match array_or(get_ty(&t.cs()[i]), "map inputs") {
                    Ok((_, v, _)) => {
                        arg_sorts_to_inner_op.push(v);
                    }
                    Err(e) => {
                        error = Some(e);
                    }
                }
            }
            match error {
                Some(e) => Err(e),
                None => {
                    let value_sort = rec_check_raw_helper(op, &arg_sorts_to_inner_op)?;
                    Ok(Sort::Array(Box::new(key_sort), Box::new(value_sort), size))
                }
            }
        }
        Op::Call(_, _, ret) => Ok(ret.clone()),
        Op::Rot(_) => Ok(get_ty(&t.cs()[0]).clone()),
        Op::PfToBoolTrusted => Ok(Sort::Bool),
        Op::ExtOp(o) => {
            let args_sorts: Vec<&Sort> = t.cs().iter().map(get_ty).collect();
            o.check(&args_sorts)
        }
        o => Err(TypeErrorReason::Custom(format!("other operator: {o}"))),
    }
}

/// Type-check this term, *non-recursively*.
/// All results are stored in the global type table.
pub fn check_raw(t: &Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.with(|types| types.borrow().get(&t.downgrade()).cloned()) {
        return Ok(s);
    }

    // lock the collector before locking TERM_TYPES
    TERM_TYPES.with(|types| {
        let mut term_tys = types.borrow_mut();
        // to_check is a stack of (node, cs checked) pairs.
        let mut to_check = vec![(t.clone(), false)];
        while !to_check.is_empty() {
            let back = to_check.last_mut().unwrap();
            let weak = back.0.downgrade();
            // The idea here is to check that
            if let Some((p, _)) = term_tys.get_key_value(&weak) {
                if p.upgrade().is_some() {
                    to_check.pop();
                    continue;
                }
                term_tys.remove(&weak);
            }
            if !back.1 {
                back.1 = true;
                for c in check_dependencies(&back.0) {
                    to_check.push((c, false));
                }
            } else {
                let ty = check_raw_step(&back.0, &term_tys).map_err(|reason| TypeError {
                    op: back.0.op().clone(),
                    args: vec![], // not quite right
                    reason,
                })?;
                term_tys.insert(back.0.downgrade(), ty);
            }
        }
        Ok(term_tys.get(&t.downgrade()).unwrap().clone())
    })
}

/// Helper function for rec_check_raw
/// Type-check given term which is expressed as
/// An operation and the sorts of its children
pub fn rec_check_raw_helper(oper: &Op, a: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    match (oper, a) {
        (Op::Eq, &[a, b]) => eq_or(a, b, "=").map(|_| Sort::Bool),
        (Op::Ite, &[&Sort::Bool, b, c]) => eq_or(b, c, "ITE").map(|_| b.clone()),
        (Op::Var(_, s), &[]) => Ok(s.clone()),
        (Op::Const(c), &[]) => Ok(c.sort()),
        (Op::BvBinOp(_), &[a, b]) => {
            let ctx = "bv binary op";
            bv_or(a, ctx)
                .and_then(|_| eq_or(a, b, ctx))
                .map(|_| a.clone())
        }
        (Op::BvBinPred(_), &[a, b]) => {
            let ctx = "bv binary predicate";
            bv_or(a, ctx)
                .and_then(|_| eq_or(a, b, ctx))
                .map(|_| Sort::Bool)
        }
        (Op::BvNaryOp(_), a) => {
            let ctx = "bv nary op";
            all_eq_or(a.iter().cloned(), ctx)
                .and_then(|t| bv_or(t, ctx))
                .map(|a| a.clone())
        }
        (Op::BvUnOp(_), &[a]) => bv_or(a, "bv unary op").map(|a| a.clone()),
        (Op::BoolToBv, &[Sort::Bool]) => Ok(Sort::BitVector(1)),
        (Op::BvExtract(high, low), &[Sort::BitVector(w)]) => {
            if low <= high && high < w {
                Ok(Sort::BitVector(high - low + 1))
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "Cannot slice from {high} to {low} in a bit-vector of width {w}"
                )))
            }
        }
        (Op::BvConcat, a) => a
            .iter()
            .try_fold(0, |w, x| match x {
                Sort::BitVector(ww) => Ok(w + ww),
                s => Err(TypeErrorReason::ExpectedBv((*s).clone(), "concat")),
            })
            .map(Sort::BitVector),
        (Op::BvSext(a), &[Sort::BitVector(b)]) => Ok(Sort::BitVector(a + b)),
        (Op::PfToBv(a), &[Sort::Field(_)]) => Ok(Sort::BitVector(*a)),
        (Op::BvUext(a), &[Sort::BitVector(b)]) => Ok(Sort::BitVector(a + b)),
        (Op::Implies, &[a, b]) => {
            let ctx = "bool binary op";
            bool_or(a, ctx)
                .and_then(|_| eq_or(a, b, ctx))
                .map(|_| a.clone())
        }
        (Op::BoolNaryOp(_), a) => {
            let ctx = "bool nary op";
            all_eq_or(a.iter().cloned(), ctx)
                .and_then(|t| bool_or(t, ctx))
                .map(|a| a.clone())
        }
        (Op::Not, &[a]) => bool_or(a, "bool unary op").map(|a| a.clone()),
        (Op::BvBit(i), &[Sort::BitVector(w)]) => {
            if i < w {
                Ok(Sort::Bool)
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "Cannot get bit {i} of a {w}-bit bit-vector"
                )))
            }
        }
        (Op::BoolMaj, &[a, b, c]) => {
            let ctx = "bool majority";
            bool_or(a, ctx)
                .and_then(|_| bool_or(b, ctx).and_then(|_| bool_or(c, ctx)))
                .map(|c| c.clone())
        }
        (Op::FpBinOp(_), &[a, b]) => {
            let ctx = "fp binary op";
            fp_or(a, ctx)
                .and_then(|_| eq_or(a, b, ctx))
                .map(|_| a.clone())
        }
        (Op::FpBinPred(_), &[a, b]) => {
            let ctx = "fp binary predicate";
            fp_or(a, ctx)
                .and_then(|_| eq_or(a, b, ctx))
                .map(|_| Sort::Bool)
        }
        (Op::FpUnOp(_), &[a]) => fp_or(a, "fp unary op").map(|a| a.clone()),
        (Op::FpUnPred(_), &[a]) => fp_or(a, "fp unary predicate").map(|_| Sort::Bool),
        (Op::BvToFp, &[Sort::BitVector(64)]) => Ok(Sort::F64),
        (Op::BvToFp, &[Sort::BitVector(32)]) => Ok(Sort::F64),
        (Op::UbvToFp(64), &[a]) => bv_or(a, "ubv-to-fp").map(|_| Sort::F64),
        (Op::UbvToFp(32), &[a]) => bv_or(a, "ubv-to-fp").map(|_| Sort::F32),
        (Op::SbvToFp(64), &[a]) => bv_or(a, "sbv-to-fp").map(|_| Sort::F64),
        (Op::SbvToFp(32), &[a]) => bv_or(a, "sbv-to-fp").map(|_| Sort::F32),
        (Op::FpToFp(64), &[a]) => fp_or(a, "fp-to-fp").map(|_| Sort::F64),
        (Op::FpToFp(32), &[a]) => fp_or(a, "fp-to-fp").map(|_| Sort::F32),
        (Op::PfNaryOp(_), a) => {
            let ctx = "pf nary op";
            all_eq_or(a.iter().cloned(), ctx)
                .and_then(|t| pf_or(t, ctx))
                .map(|a| a.clone())
        }
        (Op::UbvToPf(m), &[a]) => bv_or(a, "ubv-to-pf").map(|_| Sort::Field(m.clone())),
        (Op::PfChallenge(_, m), _) => Ok(Sort::Field(m.clone())),
        (Op::PfFitsInBits(_), &[a]) => pf_or(a, "pf fits in bits").map(|_| Sort::Bool),
        (Op::PfUnOp(_), &[a]) => pf_or(a, "pf unary op").map(|a| a.clone()),
        (Op::PfDiv, &[a, b]) => {
            eq_or(&pf_or(a, "pf / op").map(|a| a.clone())?, b, "pf / op").cloned()
        }
        (Op::IntNaryOp(_), a) => {
            let ctx = "int nary op";
            all_eq_or(a.iter().cloned(), ctx)
                .and_then(|t| int_or(t, ctx))
                .map(|a| a.clone())
        }
        (Op::IntBinPred(_), &[a, b]) => int_or(a, "int bin pred")
            .and_then(|_| int_or(b, "int bin pred"))
            .map(|_| Sort::Bool),
        (Op::Select, &[Sort::Array(k, v, _), a]) => eq_or(k, a, "select").map(|_| (**v).clone()),
        (Op::Store, &[Sort::Array(k, v, n), a, b]) => eq_or(k, a, "store")
            .and_then(|_| eq_or(v, b, "store"))
            .map(|_| Sort::Array(k.clone(), v.clone(), *n)),
        (Op::CStore, &[Sort::Array(k, v, n), a, b, c]) => eq_or(k, a, "cstore")
            .and_then(|_| eq_or(v, b, "cstore"))
            .and_then(|_| bool_or(c, "cstore"))
            .map(|_| Sort::Array(k.clone(), v.clone(), *n)),
        (Op::Fill(key_sort, size), &[v]) => Ok(Sort::Array(
            Box::new(key_sort.clone()),
            Box::new(v.clone()),
            *size,
        )),
        (Op::Array(k, v), a) => {
            let ctx = "array op";
            a.iter()
                .try_fold((), |(), ai| eq_or(v, ai, ctx).map(|_| ()))
                .map(|_| Sort::Array(Box::new(k.clone()), Box::new(v.clone()), a.len()))
        }
        (Op::Tuple, a) => Ok(Sort::Tuple(a.iter().map(|a| (*a).clone()).collect())),
        (Op::Field(i), &[a]) => tuple_or(a, "tuple field access").and_then(|t| {
            if i < &t.len() {
                Ok(t[*i].clone())
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "index {i} in tuple of sort {a}"
                )))
            }
        }),
        (Op::Update(i), &[a, b]) => tuple_or(a, "tuple field update").and_then(|t| {
            if i < &t.len() {
                eq_or(&t[*i], b, "tuple update")?;
                Ok(a.clone())
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "index {i} in tuple of sort {a}"
                )))
            }
        }),
        (Op::Map(op), a) => {
            // Check that key sorts are the same across all arrays
            // Get the value sorts of the argument arrays
            // recursively call helper to get value type of mapped array
            // then return Ok(...)

            let (key_sort, size) = match a[0].clone() {
                Sort::Array(k, _, s) => (*k, s),
                s => return Err(TypeErrorReason::ExpectedArray(s, "map")),
            };

            let mut val_sorts = Vec::new();

            for a_i in a {
                match (*a_i).clone() {
                    Sort::Array(k, v, s) => {
                        if *k != key_sort {
                            return Err(TypeErrorReason::NotEqual(*k, key_sort, "map: key sorts"));
                        }
                        if s != size {
                            return Err(TypeErrorReason::Custom(
                                "map: array lengths unequal".to_string(),
                            ));
                        }
                        val_sorts.push((*v).clone());
                    }
                    s => return Err(TypeErrorReason::ExpectedArray(s, "map")),
                };
            }

            let mut new_a = Vec::new();
            for ptr in &val_sorts {
                new_a.push(ptr);
            }
            rec_check_raw_helper(&op.clone(), &new_a[..])
                .map(|val_sort| Sort::Array(Box::new(key_sort), Box::new(val_sort), size))
        }
        (Op::Call(_, ex_args, ret), act_args) => {
            if ex_args.len() != act_args.len() {
                Err(TypeErrorReason::ExpectedArgs(ex_args.len(), act_args.len()))
            } else {
                for (e, a) in ex_args.iter().zip(act_args) {
                    eq_or(e, a, "in function call")?;
                }
                Ok(ret.clone())
            }
        }
        (Op::Rot(_), &[Sort::Array(k, v, n)]) => bv_or(k, "rot key")
            .and_then(|_| bv_or(v, "rot val"))
            .map(|_| Sort::Array(k.clone(), v.clone(), *n)),
        (Op::PfToBoolTrusted, &[k]) => pf_or(k, "pf to bool argument").map(|_| Sort::Bool),
        (Op::ExtOp(o), _) => o.check(a),
        (_, _) => Err(TypeErrorReason::Custom("other".to_string())),
    }
}
/// Type-check this term, recursively as needed.
/// All results are stored in the global type table.
pub fn rec_check_raw(t: &Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.with(|types| types.borrow().get(&t.downgrade()).cloned()) {
        return Ok(s);
    }

    TERM_TYPES.with(|types| {
        let mut term_tys = types.borrow_mut();
        // to_check is a stack of (node, cs checked) pairs.
        let mut to_check = vec![(t.clone(), false)];
        while !to_check.is_empty() {
            let back = to_check.last_mut().unwrap();
            let weak = back.0.downgrade();
            // The idea here is to check that
            if let Some((p, _)) = term_tys.get_key_value(&weak) {
                if p.upgrade().is_some() {
                    to_check.pop();
                    continue;
                } else {
                    term_tys.remove(&weak);
                }
            }
            if !back.1 {
                back.1 = true;
                // we need to end the lifetime of back before the loop starts.
                #[allow(clippy::unnecessary_to_owned)]
                for c in back.0.cs().to_vec() {
                    to_check.push((c, false));
                }
            } else {
                let tys = back
                    .0
                    .cs()
                    .iter()
                    .map(|c| term_tys.get(&c.downgrade()).unwrap())
                    .collect::<Vec<_>>();
                let ty =
                    rec_check_raw_helper(back.0.op(), &tys[..]).map_err(|reason| TypeError {
                        op: back.0.op().clone(),
                        args: tys.into_iter().cloned().collect(),
                        reason,
                    })?;
                term_tys.insert(back.0.downgrade(), ty);
            }
        }
        Ok(term_tys.get(&t.downgrade()).unwrap().clone())
    })
}

#[derive(Debug, PartialEq, Eq)]
/// A type error with some operator.
pub struct TypeError {
    op: Op,
    args: Vec<Sort>,
    reason: TypeErrorReason,
}

#[derive(Debug, PartialEq, Eq)]
/// Underlying reason for the error
pub enum TypeErrorReason {
    /// Two sorts should be equal
    NotEqual(Sort, Sort, &'static str),
    /// A sort should be boolean
    ExpectedBool(Sort, &'static str),
    /// A sort should be a floating-point
    ExpectedFp(Sort, &'static str),
    /// A sort should be a bit-vector
    ExpectedBv(Sort, &'static str),
    /// A sort should be integer
    ExpectedInt(Sort, &'static str),
    /// A sort should be a prime field
    ExpectedPf(Sort, &'static str),
    /// A sort should be an array
    ExpectedArray(Sort, &'static str),
    /// A sort should be a tuple
    ExpectedTuple(&'static str),
    /// An empty n-ary operator.
    EmptyNary(String),
    /// Expected _ args, but got _
    ExpectedArgs(usize, usize),
    /// Something else
    Custom(String),
    /// Bad bounds
    OutOfBounds(String),
}

fn bv_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    if let Sort::BitVector(_) = a {
        Ok(a)
    } else {
        Err(TypeErrorReason::ExpectedBv(a.clone(), ctx))
    }
}

fn int_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    if let Sort::Int = a {
        Ok(a)
    } else {
        Err(TypeErrorReason::ExpectedInt(a.clone(), ctx))
    }
}

pub(super) fn array_or<'a>(
    a: &'a Sort,
    ctx: &'static str,
) -> Result<(&'a Sort, &'a Sort, usize), TypeErrorReason> {
    if let Sort::Array(k, v, size) = a {
        Ok((k, v, *size))
    } else {
        Err(TypeErrorReason::ExpectedArray(a.clone(), ctx))
    }
}

fn arrmap_or<'a>(
    a: &'a Sort,
    ctx: &'static str,
) -> Result<(&'a Sort, &'a Sort, &'a usize), TypeErrorReason> {
    if let Sort::Array(k, v, s) = a {
        Ok((k, v, s))
    } else {
        Err(TypeErrorReason::ExpectedArray(a.clone(), ctx))
    }
}

fn bool_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    if let Sort::Bool = a {
        Ok(a)
    } else {
        Err(TypeErrorReason::ExpectedBool(a.clone(), ctx))
    }
}

fn fp_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    match a {
        Sort::F32 | Sort::F64 => Ok(a),
        _ => Err(TypeErrorReason::ExpectedFp(a.clone(), ctx)),
    }
}

pub(super) fn pf_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    match a {
        Sort::Field(_) => Ok(a),
        _ => Err(TypeErrorReason::ExpectedPf(a.clone(), ctx)),
    }
}

pub(super) fn tuple_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a [Sort], TypeErrorReason> {
    match a {
        Sort::Tuple(a) => Ok(a),
        _ => Err(TypeErrorReason::ExpectedTuple(ctx)),
    }
}

pub(super) fn eq_or<'a>(
    a: &'a Sort,
    b: &'a Sort,
    ctx: &'static str,
) -> Result<&'a Sort, TypeErrorReason> {
    if a == b {
        Ok(a)
    } else {
        Err(TypeErrorReason::NotEqual(a.clone(), b.clone(), ctx))
    }
}

fn all_eq_or<'a, I: Iterator<Item = &'a Sort>>(
    mut a: I,
    ctx: &'static str,
) -> Result<&'a Sort, TypeErrorReason> {
    let first = a
        .next()
        .ok_or_else(|| TypeErrorReason::EmptyNary(ctx.to_owned()))?;
    for x in a {
        if first != x {
            return Err(TypeErrorReason::NotEqual(
                (*first).clone(),
                (*x).clone(),
                ctx,
            ));
        }
    }
    Ok(first)
}
