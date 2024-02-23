//! Witness computation for Haboeck's lookup argument
//!
//! https://eprint.iacr.org/2022/1530.pdf
//!
//! Given a haystack array of values h1, ..., hN and an array of needles v1, ..., vA, outputs
//! an array of counts c1, ..., cN such that hi occurs ci times in v1, ..., vA.
//!
//! All input and output arrays must be be field -> field

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::UniqDeriGcd].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    if let &[haystack, needles] = arg_sorts {
        let (key0, value0, _n) = ty::array_or(haystack, "haystack must be an array")?;
        let (key1, value1, _a) = ty::array_or(needles, "needles must be an array")?;
        let key0 = pf_or(key0, "haystack indices must be field")?;
        let key1 = pf_or(key1, "needles indices must be field")?;
        let value0 = pf_or(value0, "haystack values must be field")?;
        let value1 = pf_or(value1, "needles values must be field")?;
        eq_or(key0, key1, "field must be the same")?;
        eq_or(key1, value0, "field must be the same")?;
        eq_or(value0, value1, "field must be the same")?;
        Ok(haystack.clone())
    } else {
        // wrong arg count
        Err(TypeErrorReason::ExpectedArgs(2, arg_sorts.len()))
    }
}

/// Evaluate [super::ExtOp::UniqDeriGcd].
pub fn eval(args: &[&Value]) -> Value {
    let haystack = args[0].as_array().values();
    let sort = args[0].sort().as_array().0.clone();
    let field = sort.as_pf().clone();
    let needles = args[1].as_array().values();
    let haystack_item_index: FxHashMap<Value, usize> = haystack
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), i))
        .collect();
    let mut counts = vec![0; haystack.len()];
    for needle in needles {
        counts[*haystack_item_index.get(&needle).expect("missing needle")] += 1;
    }
    let field_counts: Vec<Value> = counts
        .into_iter()
        .map(|c| Value::Field(field.new_v(c)))
        .collect();
    Value::Array(Array::from_vec(sort.clone(), sort, field_counts))
}
