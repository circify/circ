//! ILP-based sharing assignment
//!
//! Based on ["Efficient MPC via Program Analysis: A Framework for Efficient Optimal
//! Mixing"](https://dl.acm.org/doi/pdf/10.1145/3319535.3339818) by Ishaq, Muhammad and Milanova,
//! Ana L. and Zikas, Vassilis.

use fxhash::{FxHashMap, FxHashSet};

use super::{ShareType, SharingMap};
use crate::ir::term::*;

use crate::target::aby::assignment::CostModel;
use crate::target::ilp::{variable, Expression, Ilp, Variable};

use crate::target::aby::assignment::def_uses::*;

use std::collections::HashMap;
use std::env::var;

/// Uses an ILP to assign...
pub fn opa_smart_global_assign(
    terms: &TermSet,
    def_uses: &FxHashSet<(Term, Term)>,
    cm: &str,
    share_types: &[ShareType; 2]
) -> SharingMap {
    let base_dir = match cm {
        "opa" => "opa",
        "hycc" => "hycc",
        "empirical" => "empirical",
        "empirical_wan" => "empirical_wan",
        "synth" => "synthetic",
        _ => panic!("Unknown cost model type: {}", cm),
    };
    let p = format!(
        "{}/third_party/{}/adapted_costs.json",
        var("CARGO_MANIFEST_DIR").expect("Could not find env var CARGO_MANIFEST_DIR"),
        base_dir
    );
    let costs = CostModel::from_opa_cost_file(&p);
    build_smart_ilp(terms.clone(), def_uses, &costs, share_types)
}

fn build_smart_ilp(
    term_set: TermSet,
    def_uses: &FxHashSet<(Term, Term)>,
    costs: &CostModel,
    share_types: &[ShareType; 2]
) -> SharingMap {
    let terms: FxHashMap<Term, usize> = term_set
        .into_iter()
        .enumerate()
        .map(|(i, t)| (t, i))
        .collect();
    let mut term_vars: FxHashMap<(Term, ShareType), (Variable, f64, String)> = FxHashMap::default();
    let mut conv_vars: FxHashMap<(Term, ShareType, ShareType), (Variable, f64)> =
        FxHashMap::default();
    let mut ilp = Ilp::new();

    // build variables for all term assignments
    for (t, i) in terms.iter() {
        let mut vars = vec![];
        // println!("op: {}",&t.op);
        match &t.op {
            Op::Var(..) | Op::Const(_) => {
                for ty in share_types {
                    let name = format!("t_{}_{}", i, ty.char());
                    let v = ilp.new_variable(variable().min(0).max(1), name.clone());
                    term_vars.insert((t.clone(), *ty), (v, 0.0, name));
                    vars.push(v);
                }
            }
            // fix the select and store here for array size
            _ => {
                if let Some(costs) = costs.get(&t.op) {
                    for ty in share_types {
                        if let Some(cost) = costs.get(ty){
                            let name = format!("t_{}_{}", i, ty.char());
                            let v = ilp.new_variable(variable().min(0).max(1), name.clone());
                            term_vars.insert((t.clone(), *ty), (v, *cost, name));
                            vars.push(v);
                        }
                    }
                } else {
                    panic!("No cost for op {}", &t.op)
                }
            }
        }
        // Sum of assignments is at least 1.
        ilp.new_constraint(
            vars.into_iter()
                .fold((0.0).into(), |acc: Expression, v| acc + v)
                >> 1.0,
        );
    }

    // build variables for all conversions assignments
    for (def, use_) in def_uses {
        let def_i = terms.get(def).unwrap();
        for from_ty in share_types {
            for to_ty in share_types {
                // if def can be from_ty, and use can be to_ty
                if term_vars.contains_key(&(def.clone(), *from_ty))
                    && term_vars.contains_key(&(use_.clone(), *to_ty))
                    && from_ty != to_ty
                {
                    let v = ilp.new_variable(
                        variable().min(0).max(1),
                        format!("c_{}_{}2{}", def_i, from_ty.char(), to_ty.char()),
                    );
                    conv_vars.insert(
                        (def.clone(), *from_ty, *to_ty),
                        (v, *costs.conversions.get(&(*from_ty, *to_ty)).unwrap()),
                    );
                }
            }
        }
    }

    let def_uses_map: FxHashMap<Term, Vec<Term>> = {
        let mut t = FxHashMap::default();
        for (d, u) in def_uses {
            t.entry(d.clone()).or_insert_with(Vec::new).push(u.clone());
        }
        t
    };

    for (def, uses) in def_uses_map.iter() {
        for use_ in uses {
            for from_ty in share_types {
                for to_ty in share_types {
                    // OPA formulation:
                    // conv_from_2_to >= def_from - use_from
                    conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                        term_vars.get(&(def.clone(), *from_ty)).map(|t_from| {
                            term_vars.get(&(use_.clone(), *from_ty)).map(|t_to| {
                                ilp.new_constraint(c.0 >> (t_from.0 - t_to.0))
                            })
                        })
                    });
                }
            }
        }
    }

    ilp.maximize(
        -conv_vars
            .values()
            .map(|(a, b)| (a, b))
            .chain(term_vars.values().map(|(a, b, _)| (a, b)))
            .fold(0.0.into(), |acc: Expression, (v, cost)| acc + *v * *cost),
    );

    let (_opt, solution) = ilp.default_solve().unwrap();

    let mut assignment = TermMap::new();
    for ((term, ty), (_, _, var_name)) in &term_vars {
        if solution.get(var_name).unwrap() == &1.0 {
            assignment.insert(term.clone(), *ty);
        }
    }
    assignment
}