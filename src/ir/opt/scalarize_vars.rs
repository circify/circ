//! Replacing array and tuple variables with scalars.
use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

struct Pass;

fn create_vars(
    prefix: &str,
    sort: &Sort,
    value: Option<Value>,
    party: Option<PartyId>,
    new_var_requests: &mut Vec<(String, Sort, Option<Value>, Option<PartyId>)>,
) -> Term {
    match sort {
        Sort::Tuple(sorts) => {
            let mut values = value.map(|v| match v {
                Value::Tuple(t) => t,
                _ => panic!(),
            });
            term(
                Op::Tuple,
                sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| {
                        create_vars(
                            &format!("{}.{}", prefix, i),
                            sort,
                            values
                                .as_mut()
                                .map(|v| std::mem::replace(&mut v[i], Value::Bool(true))),
                            party,
                            new_var_requests,
                        )
                    })
                    .collect(),
            )
        }
        Sort::Array(key_s, val_s, size) => {
            let mut values = value.map(|v| match v {
                Value::Array(Array {
                    default, map, size, ..
                }) => {
                    let mut vals = vec![*default; size];
                    for (key_val, val_val) in map.into_iter() {
                        let idx = key_val.as_usize().unwrap();
                        vals[idx] = val_val;
                    }
                    vals
                }
                _ => panic!(),
            });
            make_array(
                (**key_s).clone(),
                (**val_s).clone(),
                (0..*size)
                    .map(|i| {
                        create_vars(
                            &format!("{}.{}", prefix, i),
                            val_s,
                            values
                                .as_mut()
                                .map(|v| std::mem::replace(&mut v[i], Value::Bool(true))),
                            party,
                            new_var_requests,
                        )
                    })
                    .collect(),
            )
        }
        _ => {
            new_var_requests.push((prefix.into(), sort.clone(), value, party));
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
        if let Op::Var(name, sort) = &orig.op {
            let party_visibility = computation.metadata.get_input_visibility(name);
            let mut new_var_reqs = Vec::new();
            let new = create_vars(
                name,
                sort,
                computation
                    .values
                    .as_ref()
                    .map(|v| v.get(name).unwrap().clone()),
                party_visibility,
                &mut new_var_reqs,
            );
            if new_var_reqs.len() > 0 {
                computation.replace_input(orig.clone(), new_var_reqs);
            }
            Some(new)
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
}

/// Check that every variables is a scalar.
pub fn assert_all_vars_are_scalars(cs: &Computation) {
    for t in cs
        .terms_postorder()
        .into_iter()
        .chain(cs.metadata.inputs.iter().cloned())
    {
        if let Op::Var(_name, sort) = &t.op {
            match sort {
                Sort::Array(..) | Sort::Tuple(..) => {
                    panic!("Variable {} is non-scalar", t);
                }
                _ => {}
            }
        }
    }
}
