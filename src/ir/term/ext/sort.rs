//! Sort operator

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::Sort].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    array_or(arg_sorts[0], "sort argument").map(|_| arg_sorts[0].clone())
}

/// Evaluate [super::ExtOp::Sort].
pub fn eval(args: &[&Value]) -> Value {
    let sort = args[0].sort();
    let (key_sort, value_sort, _) = sort.as_array();
    let mut values: Vec<Value> = args[0].as_array().values();
    values.sort();
    Value::Array(Array::from_vec(
        key_sort.clone(),
        value_sort.clone(),
        values,
    ))
}
