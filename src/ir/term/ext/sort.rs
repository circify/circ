//! Sort operator

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::Sort].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let [arg_sort] = ty::count_or_ref(arg_sorts)?;
    match arg_sort {
        Sort::Tuple(_) | Sort::Array(..) => Ok((**arg_sort).clone()),
        _ => Err(TypeErrorReason::Custom(
            "sort takes an array or tuple".into(),
        )),
    }
}

/// Evaluate [super::ExtOp::Sort].
pub fn eval(args: &[&Value]) -> Value {
    let sort = args[0].sort();
    let is_array = sort.is_array();
    let mut values: Vec<Value> = if is_array {
        args[0].as_array().values()
    } else {
        args[0].as_tuple().to_vec()
    };
    values.sort();
    if is_array {
        let (key_sort, value_sort, _) = sort.as_array();
        Value::Array(Array::from_vec(
            key_sort.clone(),
            value_sort.clone(),
            values,
        ))
    } else {
        Value::Tuple(values.into())
    }
}
