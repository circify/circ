//! Waksman configuration operator
//!
//! Output order: input switches, upper subnet, lower subnet, output switches

use crate::ir::term::ty::*;
use crate::ir::term::*;
use circ_waksman::{n_switches, Config};
use std::iter::FromIterator;

/// Type-check [super::ExtOp::Waksman].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let &[values] = ty::count_or_ref(arg_sorts)?;
    let (n_flows, _v_sort) = ty::homogenous_tuple_or(values, "Waksman argument")?;
    Ok(Sort::Tuple(vec![Sort::Bool; n_switches(n_flows)].into()))
}

/// Evaluate [super::ExtOp::Waksman].
pub fn eval(args: &[&Value]) -> Value {
    let values = args[0].as_tuple();
    let cfg = Config::for_sorting(values.to_vec());
    let switch_bools = Vec::from_iter(cfg.switches().into_iter().map(Value::Bool));
    assert_eq!(switch_bools.len(), n_switches(values.len()));
    Value::Tuple(switch_bools.into())
}
