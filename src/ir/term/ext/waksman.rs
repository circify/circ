//! Waksman configuration operator
//!
//! Output order: input switches, upper subnet, lower subnet, output switches

use crate::ir::term::ty::*;
use crate::ir::term::*;
use circ_waksman::{n_switches, Config};
use std::iter::FromIterator;

/// Type-check [super::ExtOp::Waksman].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    array_or(arg_sorts[0], "sort argument")
        .map(|(_, _, n_flows)| Sort::Tuple(vec![Sort::Bool; n_switches(n_flows)].into()))
}

/// Evaluate [super::ExtOp::Waksman].
pub fn eval(args: &[&Value]) -> Value {
    let len = args[0].as_array().size;
    let cfg = Config::for_sorting(args[0].as_array().values());
    let switch_bools = Vec::from_iter(cfg.switches().into_iter().map(Value::Bool));
    assert_eq!(switch_bools.len(), n_switches(len));
    Value::Tuple(switch_bools.into())
}
