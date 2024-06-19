//! Batch (multiplicative) inversion for prime field elements.
//!
//! Takes a non-empty tuple of elements from the same field and returns the inverses as a tuple of
//! the same size.

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::PfBatchInv].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let &[values] = ty::count_or_ref(arg_sorts)?;
    let (_n, v_sort) = ty::homogenous_tuple_or(values, "pf batch inversion")?;
    let _f = pf_or(v_sort, "pf_batch_inv")?;
    Ok(values.clone())
}

fn batch_inv(field: &FieldT, data: &mut [Value]) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(data.len());
    let mut tmp = field.new_v(1);
    for f in data.iter().map(Value::as_pf).filter(|f| !f.is_zero()) {
        tmp *= f;
        prod.push(tmp.clone());
    }

    // Invert `tmp`.
    tmp = tmp.recip_ref(); // Guaranteed to be nonzero.

    // Second pass: iterate backwards to compute inverses
    for (f, s) in data
        .iter_mut()
        // Backwards
        .rev()
        // Ignore normalized elements
        .filter(|f| !f.as_pf().is_zero())
        // Backwards, skip last element, fill in one for last term.
        .zip(prod.into_iter().rev().skip(1).chain(Some(field.new_v(1))))
    {
        // tmp := tmp * f; f := tmp * s = 1/f
        let new_tmp = tmp.clone() * f.as_pf();
        *f = Value::Field(tmp.clone() * &s);
        tmp = new_tmp;
    }
}

/// Evaluate [super::ExtOp::PfBatchInv].
pub fn eval(args: &[&Value]) -> Value {
    // adapted from ark_ff
    let mut values: Vec<Value> = args[0].as_tuple().to_owned();
    if !values.is_empty() {
        let field = values[0].as_pf().ty();
        batch_inv(&field, &mut values)
    }
    Value::Tuple(values.into())
}
