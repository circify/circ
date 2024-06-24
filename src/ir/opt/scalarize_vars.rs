//! Replacing array and tuple variables with scalars.
//!
//! Also replaces array and tuple *witnesses* with scalars.
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
        Sort::Array(a) => {
            let array_elements = extras::array_elements(&prefix_term);
            make_array(
                a.key.clone(),
                a.val.clone(),
                (0..a.size)
                    .zip(array_elements)
                    .map(|(i, element)| {
                        create_vars(
                            &format!("{prefix}.{i}"),
                            element,
                            &a.val,
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
            var(prefix.into(), sort.clone())
        }
    }
}

fn create_wits(prefix: &str, prefix_term: Term, sort: &Sort) -> Term {
    match sort {
        Sort::Tuple(sorts) => term(
            Op::Tuple,
            sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    create_wits(
                        &format!("{prefix}.{i}"),
                        term![Op::Field(i); prefix_term.clone()],
                        sort,
                    )
                })
                .collect(),
        ),
        Sort::Array(a) => {
            let array_elements = extras::array_elements(&prefix_term);
            make_array(
                a.key.clone(),
                a.val.clone(),
                (0..a.size)
                    .zip(array_elements)
                    .map(|(i, element)| create_wits(&format!("{prefix}.{i}"), element, &a.val))
                    .collect(),
            )
        }
        _ => term![Op::new_witness(prefix.into()); prefix_term],
    }
}

impl RewritePass for Pass {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        if let Op::Var(v) = &orig.op() {
            trace!("Considering var: {}", v.name);
            if !computation.metadata.lookup(&*v.name).committed {
                let mut new_var_reqs = Vec::new();
                let new = create_vars(&v.name, orig.clone(), &v.sort, &mut new_var_reqs, true);
                for (name, term) in new_var_reqs {
                    computation.extend_precomputation(name, term);
                }
                Some(new)
            } else {
                trace!("Skipping b/c it is commited.");
                None
            }
        } else if let Op::Witness(name) = &orig.op() {
            let sort = check(orig);
            let mut cs = rewritten_children();
            debug_assert_eq!(cs.len(), 1);
            if !sort.is_scalar() {
                trace!("Considering witness: {}", name);
            }
            Some(create_wits(name, cs.pop().unwrap(), &sort))
        } else {
            None
        }
    }
}

/// Run the tuple elimination pass.
pub fn scalarize_inputs(cs: &mut Computation) {
    let mut pass = Pass;
    pass.traverse_full(cs, false, true);
    #[cfg(debug_assertions)]
    assert_all_vars_are_scalars(cs);
    remove_non_scalar_vars_from_main_computation(cs);
}

/// Check that every variables is a scalar (or committed)
pub fn assert_all_vars_are_scalars(cs: &Computation) {
    for t in cs.terms_postorder() {
        if let Op::Var(v) = &t.op() {
            if !cs.metadata.lookup(&*v.name).committed {
                match &v.sort {
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
