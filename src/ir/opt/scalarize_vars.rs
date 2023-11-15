//! Replacing array and tuple variables with scalars.
use log::trace;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

struct Pass;

fn create_vars(
    prefix: &str,
    prefix_term: Term,
    sort: &Sort,
    new_var_requests: &mut Vec<(String, Term)>,
    top_rec_level: bool,
) -> Term {
    match sort {
        Sort::Tuple(sorts) => term(
            Op::Tuple,
            sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    create_vars(
                        &format!("{prefix}.{i}"),
                        term![Op::Field(i); prefix_term.clone()],
                        sort,
                        new_var_requests,
                        false,
                    )
                })
                .collect(),
        ),
        Sort::Array(key_s, val_s, size) => {
            let array_elements = extras::array_elements(&prefix_term);
            make_array(
                (**key_s).clone(),
                (**val_s).clone(),
                (0..*size)
                    .zip(array_elements)
                    .map(|(i, element)| {
                        create_vars(
                            &format!("{prefix}.{i}"),
                            element,
                            val_s,
                            new_var_requests,
                            false,
                        )
                    })
                    .collect(),
            )
        }
        _ => {
            // don't request a new variable if we're not recursing...
            if !top_rec_level {
                trace!("New scalar var: {}", prefix);
                new_var_requests.push((prefix.into(), prefix_term));
            }
            leaf_term(Op::Var(prefix.into(), sort.clone()))
        }
    }
}

impl RewritePass for Pass {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        _rewritten_children: F,
    ) -> Option<Term> {
        if let Op::Var(name, sort) = &orig.op() {
            trace!("Considering var: {}", name);
            if !computation.metadata.lookup(name).committed {
                let mut new_var_reqs = Vec::new();
                let new = create_vars(name, orig.clone(), sort, &mut new_var_reqs, true);
                for (name, term) in new_var_reqs {
                    computation.extend_precomputation(name, term);
                }
                Some(new)
            } else {
                trace!("Skipping b/c it is commited.");
                None
            }
        } else {
            None
        }
    }
}

/// Run the tuple elimination pass.
pub fn scalarize_inputs(cs: &mut Computation) {
    let mut pass = Pass;
    pass.traverse(cs);
    #[cfg(debug_assertions)]
    assert_all_vars_are_scalars(cs);
    remove_non_scalar_vars_from_main_computation(cs);
}

/// Check that every variables is a scalar (or committed)
pub fn assert_all_vars_are_scalars(cs: &Computation) {
    for t in cs.terms_postorder() {
        if let Op::Var(name, sort) = &t.op() {
            if !cs.metadata.lookup(name).committed {
                match sort {
                    Sort::Array(..) | Sort::Tuple(..) => {
                        panic!("Variable {} is non-scalar", t);
                    }
                    _ => {}
                }
            }
        }
    }
}

/// Remove all variables that are non-scalar (and not committed).
fn remove_non_scalar_vars_from_main_computation(cs: &mut Computation) {
    for input in cs.metadata.ordered_inputs() {
        let name = input.as_var_name();
        if !check(&input).is_scalar() && !cs.metadata.lookup(&name).committed {
            cs.metadata.remove_var(name);
        }
    }
    assert_all_vars_are_scalars(cs);
}
