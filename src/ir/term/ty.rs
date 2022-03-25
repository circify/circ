//! Type(Sort)-checking

use super::*;

lazy_static! {
    /// Cache of all types
    pub(super) static ref TERM_TYPES: RwLock<TypeTable> = RwLock::new(TypeTable {
        map: FxHashMap::default(),
        last_len: 0,
    });
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

/// Type-check this term, *non-recursively*.
/// All results are stored in the global type table.
pub fn check_raw(t: &Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.read().unwrap().get(&t.to_weak()) {
        return Ok(s.clone());
    }
    // RSW: the below loop is a band-aid to keep from blowing the stack
    // XXX(q) is there a better way to write this function?
    let mut t = t;
    loop {
        let t_new = match &t.op {
            Op::Ite => &t.cs[1],
            Op::BvBinOp(_) => &t.cs[0],
            Op::BvNaryOp(_) => &t.cs[0],
            Op::BvUnOp(_) => &t.cs[0],
            Op::FpBinOp(_) => &t.cs[0],
            Op::FpUnOp(_) => &t.cs[0],
            Op::PfUnOp(_) => &t.cs[0],
            Op::PfNaryOp(_) => &t.cs[0],
            Op::Store => &t.cs[0],
            Op::Update(_i) => &t.cs[0],
            _ => break,
        };
        if std::ptr::eq(t, t_new) {
            panic!("infinite loop detected in check_raw");
        }
        t = t_new;
    }
    let ty = match &t.op {
        Op::Ite => Ok(check_raw(&t.cs[1])?),
        Op::Eq => Ok(Sort::Bool),
        Op::Var(_, s) => Ok(s.clone()),
        Op::Const(c) => Ok(c.sort()),
        Op::BvBinOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::BvBinPred(_) => Ok(Sort::Bool),
        Op::BvNaryOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::BvUnOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::BoolToBv => Ok(Sort::BitVector(1)),
        Op::BvExtract(a, b) => Ok(Sort::BitVector(a - b + 1)),
        Op::BvConcat => t
            .cs
            .iter()
            .map(check_raw)
            .try_fold(
                Ok(0),
                |l: Result<usize, TypeErrorReason>,
                 r: Result<Sort, TypeError>|
                 -> Result<Result<usize, TypeErrorReason>, TypeError> {
                    r.map(|rr| l.and_then(|lll| bv_or(&rr, "concat").map(|rrr| lll + rrr.as_bv())))
                },
            )?
            .map(Sort::BitVector),
        Op::BvUext(a) => {
            bv_or(&check_raw(&t.cs[0])?, "bv-uext").map(|bv| Sort::BitVector(bv.as_bv() + a))
        }
        Op::BvSext(a) => {
            bv_or(&check_raw(&t.cs[0])?, "bv-uext").map(|bv| Sort::BitVector(bv.as_bv() + a))
        }
        Op::PfToBv(a) => Ok(Sort::BitVector(*a)),
        Op::Implies => Ok(Sort::Bool),
        Op::BoolNaryOp(_) => Ok(Sort::Bool),
        Op::Not => Ok(Sort::Bool),
        Op::BvBit(_) => Ok(Sort::Bool),
        Op::BoolMaj => Ok(Sort::Bool),
        Op::FpBinOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::FpBinPred(_) => Ok(Sort::Bool),
        Op::FpUnPred(_) => Ok(Sort::Bool),
        Op::FpUnOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::BvToFp => match bv_or(&check_raw(&t.cs[0])?, "bv-to-fp") {
            Ok(Sort::BitVector(32)) => Ok(Sort::F32),
            Ok(Sort::BitVector(64)) => Ok(Sort::F64),
            Ok(s) => Err(TypeErrorReason::Custom(format!(
                "Cannot convert {} to floating-point",
                s
            ))),
            Err(e) => Err(e),
        },
        Op::UbvToFp(64) => Ok(Sort::F64),
        Op::UbvToFp(32) => Ok(Sort::F32),
        Op::SbvToFp(64) => Ok(Sort::F64),
        Op::SbvToFp(32) => Ok(Sort::F32),
        Op::FpToFp(64) => Ok(Sort::F64),
        Op::FpToFp(32) => Ok(Sort::F32),
        Op::PfUnOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::PfNaryOp(_) => Ok(check_raw(&t.cs[0])?),
        Op::UbvToPf(m) => Ok(Sort::Field(m.clone())),
        Op::Select => array_or(&check_raw(&t.cs[0])?, "select").map(|(_, v)| v.clone()),
        Op::Store => Ok(check_raw(&t.cs[0])?),
        Op::Tuple => Ok(Sort::Tuple(
            t.cs.iter().map(check_raw).collect::<Result<_, _>>()?,
        )),
        Op::Field(i) => {
            let sort = check_raw(&t.cs[0])?;
            let sorts = sort.as_tuple();
            if i < &sorts.len() {
                Ok(sorts[*i].clone())
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "index {} in tuple of sort {}",
                    i, sort
                )))
            }
        }
        Op::Update(_i) => Ok(check_raw(&t.cs[0])?),
        Op::Map(op) => {
            let arg_cnt = t.cs.len();
            let mut dterm_cs = Vec::new();

            let mut key_sort = Sort::Bool;
            let mut size = 0;
            let mut error = None;

            match arrmap_or(&check_raw(&t.cs[0])?, "map") {
                Ok((k, _, s)) => {
                    key_sort = k.clone();
                    size = s.clone();
                }
                Err(e) => {
                    error = Some(e);
                }
            }

            for i in 0..arg_cnt {
                match array_or(&check_raw(&t.cs[i])?, "map inputs") {
                    Ok((_, v)) => {
                        dterm_cs.push(v.default_term());
                    }
                    Err(e) => {
                        error = Some(e);
                    }
                }
            }

            match error {
                Some(e) => Err(e),
                None => {
                    let dummy_term = term((**op).clone(), dterm_cs);
                    let res_sort = check_raw(&dummy_term)
                        .map(|val_sort| Sort::Array(Box::new(key_sort), Box::new(val_sort), size));

                    match res_sort {
                        Ok(s) => Ok(s),
                        _ => Err(TypeErrorReason::Custom("map failed".to_string())),
                    }
                }
            }
        }
        o => Err(TypeErrorReason::Custom(format!("other operator: {}", o))),
    };
    let mut term_tys = TERM_TYPES.write().unwrap();
    let ty = ty.map_err(|reason| TypeError {
        op: t.op.clone(),
        args: vec![], // not quite right..
        reason,
    })?;
    term_tys.insert(t.to_weak(), ty.clone());
    Ok(ty)
}

/// Helper functio for rec_check_raw
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
                    "Cannot slice from {} to {} in a bit-vector of width {}",
                    high, low, w
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
                    "Cannot get bit {} of a {}-bit bit-vector",
                    i, w
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
        (Op::UbvToPf(m), &[a]) => bv_or(a, "sbv-to-fp").map(|_| Sort::Field(m.clone())),
        (Op::PfUnOp(_), &[a]) => pf_or(a, "pf unary op").map(|a| a.clone()),
        (Op::Select, &[Sort::Array(k, v, _), a]) => eq_or(k, a, "select").map(|_| (**v).clone()),
        (Op::Store, &[Sort::Array(k, v, n), a, b]) => eq_or(k, a, "store")
            .and_then(|_| eq_or(v, b, "store"))
            .map(|_| Sort::Array(k.clone(), v.clone(), *n)),
        (Op::Tuple, a) => Ok(Sort::Tuple(a.iter().map(|a| (*a).clone()).collect())),
        (Op::Field(i), &[a]) => tuple_or(a, "tuple field access").and_then(|t| {
            if i < &t.len() {
                Ok(t[*i].clone())
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "index {} in tuple of sort {}",
                    i, a
                )))
            }
        }),
        (Op::Update(i), &[a, b]) => tuple_or(a, "tuple field update").and_then(|t| {
            if i < &t.len() {
                eq_or(&t[*i], b, "tuple update")?;
                Ok(a.clone())
            } else {
                Err(TypeErrorReason::OutOfBounds(format!(
                    "index {} in tuple of sort {}",
                    i, a
                )))
            }
        }),
        (Op::Map(op), a) => {
            //TODO:
            // Check that key sorts are the same across all arrays
            // Get the value sorts of the argument arrays
            // recursively call helper to get value type of mapped array
            // then return Ok(...)
            let arg_cnt = a.len();

            let key_sort = match a[0].clone() {
                Sort::Array(k, _, _) => *k.clone(),
                s => return Err(TypeErrorReason::ExpectedArray(s.clone(), "map")),
            };

            let mut val_sorts = Vec::new();
            for i in 0..arg_cnt {
                match a[i].clone() {
                    Sort::Array(k, v, _) => {
                        if *k != key_sort {
                            return Err(TypeErrorReason::NotEqual(
                                *k.clone(),
                                key_sort.clone(),
                                "map",
                            ));
                        }
                        val_sorts.push((*v).clone());
                    }
                    s => return Err(TypeErrorReason::ExpectedArray(s.clone(), "map")),
                };
            }

            let mut new_a = Vec::new();
            for i in 0..arg_cnt {
                new_a.push(&val_sorts[i]);
            }

            rec_check_raw_helper(&(*op.clone()), &new_a[..])
        }
        (_, _) => Err(TypeErrorReason::Custom("other".to_string())),
    }
}
/// Type-check this term, recursively as needed.
/// All results are stored in the global type table.
pub fn rec_check_raw(t: &Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.read().unwrap().get(&t.to_weak()) {
        return Ok(s.clone());
    }
    {
        let mut term_tys = TERM_TYPES.write().unwrap();
        // to_check is a stack of (node, cs checked) pairs.
        let mut to_check = vec![(t.clone(), false)];
        while !to_check.is_empty() {
            let back = to_check.last_mut().unwrap();
            let weak = back.0.to_weak();
            // The idea here is to check that
            if let Some((p, _)) = term_tys.get_key_value(&weak) {
                if p.to_hconsed().is_some() {
                    to_check.pop();
                    continue;
                } else {
                    term_tys.remove(&weak);
                }
            }
            if !back.1 {
                back.1 = true;
                for c in back.0.cs.clone() {
                    to_check.push((c, false));
                }
            } else {
                let tys = back
                    .0
                    .cs
                    .iter()
                    .map(|c| term_tys.get(&c.to_weak()).unwrap())
                    .collect::<Vec<_>>();

                let ty =
                    rec_check_raw_helper(&back.0.op, &tys[..]).map_err(|reason| TypeError {
                        op: back.0.op.clone(),
                        args: tys.into_iter().cloned().collect(),
                        reason,
                    })?;
                term_tys.insert(back.0.to_weak(), ty);
            }
        }
    }
    Ok(TERM_TYPES
        .read()
        .unwrap()
        .get(&t.to_weak())
        .unwrap()
        .clone())
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
    /// A sort should be a boolean
    ExpectedBool(Sort, &'static str),
    /// A sort should be a floating-point
    ExpectedFp(Sort, &'static str),
    /// A sort should be a bit-vector
    ExpectedBv(Sort, &'static str),
    /// A sort should be a prime field
    ExpectedPf(Sort, &'static str),
    /// A sort should be an array
    ExpectedArray(Sort, &'static str),
    /// A sort should be a tuple
    ExpectedTuple(&'static str),
    /// An empty n-ary operator.
    EmptyNary(String),
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

fn array_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<(&'a Sort, &'a Sort), TypeErrorReason> {
    if let Sort::Array(k, v, _) = a {
        Ok((&*k, &*v))
    } else {
        Err(TypeErrorReason::ExpectedArray(a.clone(), ctx))
    }
}

fn arrmap_or<'a>(
    a: &'a Sort,
    ctx: &'static str,
) -> Result<(&'a Sort, &'a Sort, &'a usize), TypeErrorReason> {
    if let Sort::Array(k, v, s) = a {
        Ok((&*k, &*v, &*s))
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

fn pf_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    match a {
        Sort::Field(_) => Ok(a),
        _ => Err(TypeErrorReason::ExpectedPf(a.clone(), ctx)),
    }
}

fn tuple_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a [Sort], TypeErrorReason> {
    match a {
        Sort::Tuple(a) => Ok(a),
        _ => Err(TypeErrorReason::ExpectedTuple(ctx)),
    }
}

fn eq_or(a: &Sort, b: &Sort, ctx: &'static str) -> Result<(), TypeErrorReason> {
    if a == b {
        Ok(())
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
