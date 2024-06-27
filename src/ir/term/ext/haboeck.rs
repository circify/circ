//! Witness computation for Haboeck's lookup argument
//!
//! <https://eprint.iacr.org/2022/1530.pdf>
//!
//! Given a haystack array of values h1, ..., hN and an array of needles v1, ..., vA, outputs
//! an array of counts c1, ..., cN such that hI occurs cI times in v1, ..., vA.
//!
//! All input and output arrays must be be field -> field

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::Haboeck].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let &[haystack, needles] = ty::count_or_ref(arg_sorts)?;
    let (_n, value0) = ty::homogenous_tuple_or(haystack, "haystack must be a tuple")?;
    let (_a, value1) = ty::homogenous_tuple_or(needles, "needles must be a tuple")?;
    let value0 = pf_or(value0, "haystack values must be field")?;
    let value1 = pf_or(value1, "needles values must be field")?;
    eq_or(value0, value1, "field must be the same")?;
    Ok(haystack.clone())
}

/// Evaluate [super::ExtOp::Haboeck].
pub fn eval(args: &[&Value]) -> Value {
    let haystack: Vec<FieldV> = args[0]
        .as_tuple()
        .iter()
        .map(|v| v.as_pf().clone())
        .collect();
    let needles: Vec<FieldV> = args[1]
        .as_tuple()
        .iter()
        .map(|v| v.as_pf().clone())
        .collect();
    let field = haystack[0].ty();
    let haystack_item_index: FxHashMap<FieldV, usize> = haystack
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), i))
        .collect();
    let mut counts = vec![0; haystack.len()];
    for needle in needles {
        if let Some(idx) = haystack_item_index.get(&needle) {
            counts[*idx] += 1;
        } else {
            panic!(
                "missing needle\nhaystack: {:?}, needle: {}",
                haystack, needle
            )
        }
    }
    let field_counts: Vec<Value> = counts
        .into_iter()
        .map(|c| Value::Field(field.new_v(c)))
        .collect();
    Value::Tuple(field_counts.into())
}
