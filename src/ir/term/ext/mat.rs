//! Matrix operators: [super::ExtOp::MatMul] and [super::ExtOp::MatAdd].
//!
//! A matrix over a prime field is an array of rows, `(array F (array F F c) r)`,
//! so `m[i][j]` is `(select (select m i) j)`. Shapes are read off the argument
//! sorts, so the operators carry no sizes of their own.
//!
//! They exist so that the compiler can *see* a matrix product. The randomized
//! matrix-multiply transform ([crate::ir::opt::mat]) replaces the products the
//! verifier would evaluate with a prover-supplied product plus a Freivalds
//! check, and lowers the rest to field arithmetic. Since they also evaluate, a
//! product the *prover* computes can stay as one of these in a precompute,
//! where it costs the verifier nothing.

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// The `(rows, cols, index sort, entry field)` of a matrix sort.
pub fn shape_or<'a>(
    s: &'a Sort,
    ctx: &'static str,
) -> Result<(usize, usize, &'a Sort, &'a Sort), TypeErrorReason> {
    let (key, row, rows) = array_or(s, ctx)?;
    pf_or(key, ctx)?;
    let (row_key, entry, cols) = array_or(row, ctx)?;
    eq_or(key, row_key, ctx)?;
    let f = pf_or(entry, ctx)?;
    Ok((rows, cols, key, f))
}

/// The sort of an `r` by `c` matrix indexed by `key`, with entries in `f`.
pub fn matrix_sort(key: &Sort, f: &Sort, r: usize, c: usize) -> Sort {
    Sort::new_array(key.clone(), Sort::new_array(key.clone(), f.clone(), c), r)
}

/// Type-check [super::ExtOp::MatMul].
pub fn check_mul(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let &[a, b] = ty::count_or_ref(arg_sorts)?;
    let (r, k, key, f) = shape_or(a, "matmul: left argument")?;
    let (k2, c, key2, f2) = shape_or(b, "matmul: right argument")?;
    eq_or(key, key2, "matmul: index sorts")?;
    eq_or(f, f2, "matmul: entry fields")?;
    if k != k2 {
        return Err(TypeErrorReason::Custom(format!(
            "matmul: inner dimensions differ: {k} and {k2}"
        )));
    }
    Ok(matrix_sort(key, f, r, c))
}

/// Type-check [super::ExtOp::MatAdd].
pub fn check_add(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let &[a, b] = ty::count_or_ref(arg_sorts)?;
    shape_or(a, "matadd: left argument")?;
    shape_or(b, "matadd: right argument")?;
    eq_or(a, b, "matadd: arguments must have the same shape")?;
    Ok(a.clone())
}

/// A matrix value's entries, by row.
fn rows(v: &Value) -> Vec<Vec<FieldV>> {
    v.as_array()
        .values()
        .iter()
        .map(|row| {
            row.as_array()
                .values()
                .iter()
                .map(|e| e.as_pf().clone())
                .collect()
        })
        .collect()
}

/// A matrix value from its entries, by row.
fn from_rows(key: &Sort, f: &FieldT, rows: Vec<Vec<FieldV>>) -> Value {
    let cols = rows[0].len();
    let entry_sort = Sort::Field(f.clone());
    let items: Vec<Value> = rows
        .into_iter()
        .map(|row| {
            Value::Array(Array::from_vec(
                key.clone(),
                entry_sort.clone(),
                row.into_iter().map(Value::Field).collect(),
            ))
        })
        .collect();
    Value::Array(Array::from_vec(
        key.clone(),
        Sort::new_array(key.clone(), entry_sort, cols),
        items,
    ))
}

/// Evaluate [super::ExtOp::MatMul].
pub fn eval_mul(args: &[&Value]) -> Value {
    let a = rows(args[0]);
    let b = rows(args[1]);
    let key = &args[0].as_array().key_sort;
    let f = a[0][0].ty();
    let (rs, ks, cs) = (a.len(), b.len(), b[0].len());
    let out = (0..rs)
        .map(|i| {
            (0..cs)
                .map(|j| {
                    let mut s = f.new_v(0);
                    for k in 0..ks {
                        s += &(a[i][k].clone() * &b[k][j]);
                    }
                    s
                })
                .collect()
        })
        .collect();
    from_rows(key, &f, out)
}

/// Evaluate [super::ExtOp::MatAdd].
pub fn eval_add(args: &[&Value]) -> Value {
    let a = rows(args[0]);
    let b = rows(args[1]);
    let key = &args[0].as_array().key_sort;
    let f = a[0][0].ty();
    let out = a
        .into_iter()
        .zip(b)
        .map(|(ra, rb)| ra.into_iter().zip(rb).map(|(x, y)| x + &y).collect())
        .collect();
    from_rows(key, &f, out)
}
