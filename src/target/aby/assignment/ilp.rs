//! ILP-based sharing assignment
//!
//! Loosely based on ["Efficient MPC via Program Analysis: A Framework for Efficient Optimal
//! Mixing"](https://dl.acm.org/doi/pdf/10.1145/3319535.3339818) by Ishaq, Muhammad and Milanova,
//! Ana L. and Zikas, Vassilis.
//!
//! Our actual ILP is as follows:
//!
//! Let `s`, `t` denote terms, and `a`, `b` denote protocols.
//!
//! Let `T[t, a]` be a binary variable indicating whether term `t` is evaluated using protocol `a`.
//! Let `C[t, a, b]` be a binary variable indicating whether term `t` needs to be converted from
//! `a` to `b`.
//!
//! Since each term is evaluated using one protocol,
//!
//! `forall t. 1 = \sum_a T[t, a]             (1)`
//!
//! Sometimes conversions are needed
//!
//! `forall t a b. forall s in Uses(t). C[t, a, b] >= T[t, a] + T[s, b] - 1     (2)`
//!
//! The constraint (2) is intendend to encode
//!
//! `forall t a b. C[t, a, b] = OR_(s in Uses(t)) T[t, a] AND T[s, b]`
//!
//! It does this well because (a) the system is SAT and (b) our objective is a linear combination
//! of all variables (term and conversion) scaled by their cost. In trying to minimize that, `C`
//! will be set to the smallest value possible (0) if either of the variables on the right of (2)
//! are 0.  If they are both 1 (for ANY `s`), then it must be 1.

use fxhash::{FxHashMap, FxHashSet};

use super::{ShareType, SharingMap, SHARE_TYPES};
use crate::ir::term::*;

use crate::target::aby::assignment::CostModel;
use crate::target::ilp::{variable, Expression, Ilp, Variable};

use crate::target::aby::assignment::def_uses::*;

use std::collections::HashMap;
use std::env::var;

/// Uses an ILP to assign...
pub fn assign(c: &ComputationSubgraph, cm: &str) -> SharingMap {
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
    build_ilp(c, &costs)
}

/// Uses an ILP to assign and abandon the outer assignments
pub fn assign_mut(c: &ComputationSubgraph, cm: &str, co: &ComputationSubgraph) -> SharingMap {
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
    let mut smap = TermMap::new();
    let mut cnt = 1;
    while smap.len() == 0 {
        // A hack for empty result during multi-threading
        // Simply retry until get a non-empty result
        if cnt > 5 {
            panic!("MT BUG: Dead loop.")
        }
        smap = build_ilp(c, &costs);
        cnt = cnt + 1;
    }
    let mut trunc_smap = TermMap::new();
    for node in co.nodes.clone() {
        let share = smap.get_mut(&node).unwrap();
        trunc_smap.insert(node, *share);
    }
    trunc_smap
}

/// Uses an ILP to assign and abandon the outer assignments
pub fn assign_mut_smart(
    dusg: &DefUsesSubGraph,
    cm: &str,
    dusg_ref: &TermSet,
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
    let mut smap = TermMap::new();
    let mut cnt = 1;
    while smap.len() == 0 {
        // A hack for empty result during multi-threading
        // Simply retry until get a non-empty result
        if cnt > 5 {
            panic!("MT BUG: Dead loop.")
        }
        smap = build_smart_ilp(dusg.nodes.clone(), &dusg.def_use, &costs);
        cnt = cnt + 1;
    }
    let mut trunc_smap = TermMap::new();
    for node in dusg_ref.iter() {
        let share = smap.get_mut(&node).unwrap();
        trunc_smap.insert(node.clone(), *share);
    }
    trunc_smap
}

/// Uses an ILP to assign...
pub fn smart_global_assign(
    terms: &TermSet,
    def_uses: &FxHashSet<(Term, Term)>,
    cm: &str,
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
    build_smart_ilp(terms.clone(), def_uses, &costs)
}

fn build_smart_ilp(
    term_set: TermSet,
    def_uses: &FxHashSet<(Term, Term)>,
    costs: &CostModel,
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
                for ty in &SHARE_TYPES {
                    let name = format!("t_{}_{}", i, ty.char());
                    let v = ilp.new_variable(variable().binary(), name.clone());
                    // if *ty == ShareType::Arithmetic {
                    //     term_vars.insert((t.clone(), *ty), (v, 0.1, name));
                    // } else if *ty == ShareType::Boolean{
                    //     term_vars.insert((t.clone(), *ty), (v, 0.12, name));
                    // } else{
                    //     term_vars.insert((t.clone(), *ty), (v, 0.11, name));
                    // }
                    term_vars.insert((t.clone(), *ty), (v, 0.0, name));
                    vars.push(v);
                }
            }
            // fix the select and store here for array size
            _ => {
                if let Some(costs) = costs.get(&t.op) {
                    for (ty, cost) in costs {
                        let name = format!("t_{}_{}", i, ty.char());
                        let v = ilp.new_variable(variable().binary(), name.clone());
                        term_vars.insert((t.clone(), *ty), (v, *cost, name));
                        vars.push(v);
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
        // println!("def op: {}", def.op);
        // println!("use op: {}", use_.op);
        let def_i = terms.get(def).unwrap();
        for from_ty in &SHARE_TYPES {
            for to_ty in &SHARE_TYPES {
                // if def can be from_ty, and use can be to_ty
                if term_vars.contains_key(&(def.clone(), *from_ty))
                    && term_vars.contains_key(&(use_.clone(), *to_ty))
                    && from_ty != to_ty
                {
                    let v = ilp.new_variable(
                        variable().binary(),
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
            for from_ty in &SHARE_TYPES {
                for to_ty in &SHARE_TYPES {
                    let ilp_version = true;
                    if ilp_version {
                        conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                            term_vars.get(&(def.clone(), *from_ty)).map(|t_from| {
                                // c[term i from pi to pi'] >= t[term j with pi'] + t[term i with pi] - 1
                                term_vars.get(&(use_.clone(), *to_ty)).map(|t_to| {
                                    ilp.new_constraint(c.0 >> (t_from.0 + t_to.0 - 1.0))
                                })
                            })
                        });
                    } else {
                        // hardcoding here
                        // a2b > y2b
                        // y2a > b2a
                        // a2y > b2y
                        if *from_ty == ShareType::Arithmetic && *to_ty == ShareType::Boolean {
                            let cheap_ty = ShareType::Yao;
                            conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                term_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    term_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        term_vars.get(&(def.clone(), cheap_ty)).map(|d_ch| {
                                            term_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                                ilp.new_constraint(
                                                    c.0 >> (d_from.0 + u_to.0
                                                        - 1.0
                                                        - d_to.0
                                                        - d_ch.0),
                                                )
                                            })
                                        })
                                    })
                                })
                            });
                        } else if *from_ty == ShareType::Yao && *to_ty == ShareType::Arithmetic {
                            let cheap_ty = ShareType::Boolean;
                            conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                term_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    term_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        term_vars.get(&(def.clone(), cheap_ty)).map(|d_ch| {
                                            term_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                                ilp.new_constraint(
                                                    c.0 >> (d_from.0 + u_to.0
                                                        - 1.0
                                                        - d_to.0
                                                        - d_ch.0),
                                                )
                                            })
                                        })
                                    })
                                })
                            });
                        } else if *from_ty == ShareType::Arithmetic && *to_ty == ShareType::Yao {
                            let cheap_ty = ShareType::Boolean;
                            conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                term_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    term_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        term_vars.get(&(def.clone(), cheap_ty)).map(|d_ch| {
                                            term_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                                ilp.new_constraint(
                                                    c.0 >> (d_from.0 + u_to.0
                                                        - 1.0
                                                        - d_to.0
                                                        - d_ch.0),
                                                )
                                            })
                                        })
                                    })
                                })
                            });
                        } else {
                            conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                term_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    term_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        term_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                            ilp.new_constraint(
                                                c.0 >> (d_from.0 + u_to.0 - 1.0 - d_to.0),
                                            )
                                        })
                                    })
                                })
                            });
                        }
                    }
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
            // if assignment.contains_key(term){
            //     println!("Duplicate assignment found: {}!!!", term.op);
            // }
            // if *ty == ShareType::Boolean{
            //     println!("Boolean assignment found: {}!!!", term.op);
            //     if let Some(uses) = def_uses_map.get(term){
            //         for t in uses.iter(){
            //             println!("uses: {}!!!", t.op);
            //         }
            //     }
            // }
            assignment.insert(term.clone(), *ty);
        }
    }
    assignment
}

fn build_ilp(c: &ComputationSubgraph, costs: &CostModel) -> SharingMap {
    let mut terms: TermSet = TermSet::new();
    let mut def_uses: FxHashSet<(Term, Term)> = FxHashSet::default();
    for (node, edges) in c.edges.clone() {
        terms.insert(node.clone());
        for c in edges.iter() {
            def_uses.insert((c.clone(), node.clone()));
        }
    }
    let terms: FxHashMap<Term, usize> =
        terms.into_iter().enumerate().map(|(i, t)| (t, i)).collect();
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
                for ty in &SHARE_TYPES {
                    let name = format!("t_{}_{}", i, ty.char());
                    let v = ilp.new_variable(variable().binary(), name.clone());
                    term_vars.insert((t.clone(), *ty), (v, 0.0, name));
                    vars.push(v);
                }
            }
            _ => {
                if let Some(costs) = costs.get(&t.op) {
                    for (ty, cost) in costs {
                        let name = format!("t_{}_{}", i, ty.char());
                        let v = ilp.new_variable(variable().binary(), name.clone());
                        term_vars.insert((t.clone(), *ty), (v, *cost, name));
                        vars.push(v);
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
    for (def, use_) in &def_uses {
        let def_i = terms.get(def).unwrap();
        for from_ty in &SHARE_TYPES {
            for to_ty in &SHARE_TYPES {
                // if def can be from_ty, and use can be to_ty
                if term_vars.contains_key(&(def.clone(), *from_ty))
                    && term_vars.contains_key(&(use_.clone(), *to_ty))
                    && from_ty != to_ty
                {
                    let v = ilp.new_variable(
                        variable().binary(),
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

    let def_uses: FxHashMap<Term, Vec<Term>> = {
        let mut t = FxHashMap::default();
        for (d, u) in def_uses {
            t.entry(d).or_insert_with(Vec::new).push(u);
        }
        t
    };

    for (def, uses) in def_uses {
        for use_ in uses {
            for from_ty in &SHARE_TYPES {
                for to_ty in &SHARE_TYPES {
                    conv_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                        term_vars.get(&(def.clone(), *from_ty)).map(|t_from| {
                            // c[term i from pi to pi'] >= t[term j with pi'] + t[term i with pi] - 1
                            term_vars
                                .get(&(use_.clone(), *to_ty))
                                .map(|t_to| ilp.new_constraint(c.0 >> (t_from.0 + t_to.0 - 1.0)))
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

/// Use a ILP to find a optimal combination of mutation assignments
pub fn comb_selection(
    mut_maps: &HashMap<usize, HashMap<usize, SharingMap>>,
    cs_map: &HashMap<usize, ComputationSubgraph>,
    cm: &str,
) -> HashMap<usize, SharingMap> {
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
    build_comb_ilp(mut_maps, cs_map, &costs)
}

/**
 * Combination algo:
 *
 * Notations:
 *  - P ^ i: partitions
 *  - l^i_j: assignment j for P^i
 *  - C^i_j: inner cost (node and inner edges) of P^i with l^i_j
 *  - X^i_j: Assign l^i_j to P^i
 *  - K_{p, p'}: conversion cost from p to p'
 *  - v^i_{k,p}: (edge) vertex k in partition P^i with assignment p
 *  - B^i_{k, p}: Set of indices j such that l^i_j assign p to k
 *  - E_{u, w, p, p'}: cross partition edges that assign u, w with p, p' repsectively
 *
 * Constraints:
 *  - [ for any i, \sum_j X^i_j >= 1 ]: Each partition must have a assignment
 *  - [ for any i,k,  \sum_p v^i_{k, p} >= 1 ]: Each node must have a assignment
 *  - [ E_{u, w, p, p'} >= v{u, p} + v{w, p'} - 1 ]: Edge is added if u and v is assigned with p and p' resp.
 *  
 * Object:
 *  - min[\sum_{i, j} C^i_j X^i_j + \sum E{u,w,p,p'}K_{p, p'}]
 *
 */

fn build_comb_ilp(
    mut_maps: &HashMap<usize, HashMap<usize, SharingMap>>,
    cs_map: &HashMap<usize, ComputationSubgraph>,
    costs: &CostModel,
) -> HashMap<usize, SharingMap> {
    // global vars
    let mut ilp = Ilp::new();

    let mut x_vars: FxHashMap<(usize, usize), (Variable, f64, String)> = FxHashMap::default();
    let mut v_vars: FxHashMap<(Term, ShareType), (Variable, f64, String)> = FxHashMap::default();
    let mut e_vars: FxHashMap<(Term, ShareType, ShareType), (Variable, f64)> = FxHashMap::default();

    let mut b_set: FxHashMap<(usize, Term, ShareType), Vec<Variable>> = FxHashMap::default();

    // build variables for selection in each partition X^i_j
    for (pid, smaps) in mut_maps.iter() {
        let mut vars = vec![];
        for (mid, maps) in smaps.iter() {
            let name = format!("X_{}_{}", pid, mid);
            let v = ilp.new_variable(variable().binary(), name.clone());
            // TODO: update this buggy function
            let map_cost = calculate_cost(&maps, costs);
            x_vars.insert((*pid, *mid), (v, map_cost, name));
            vars.push(v);
        }
        // Sum of assignment selection is at least 1
        ilp.new_constraint(
            vars.into_iter()
                .fold((0.0).into(), |acc: Expression, v| acc + v)
                >> 1.0,
        );
    }

    // build b set
    // build variables for each edge node v^i_{k,p}
    let mut edge_terms: FxHashSet<(usize, usize, Term)> = FxHashSet::default();
    let mut def_uses: FxHashSet<(Term, Term, usize, usize)> = FxHashSet::default();
    for (pid, cs) in cs_map.iter() {
        let mut index: usize = 1;
        for t in cs.ins.clone() {
            edge_terms.insert((*pid, index, t.clone()));
            index = index + 1;
            // get all cross partition egdes:
            for outer_node in t.cs.iter() {
                def_uses.insert((outer_node.clone(), t.clone(), *pid, index));
            }
        }
        for t in cs.outs.clone() {
            edge_terms.insert((*pid, index, t.clone()));
            index = index + 1;
        }
    }

    for (pid, i, t) in edge_terms.iter() {
        let mut vars = vec![];
        match &t.op {
            Op::Var(..) | Op::Const(_) => {
                for ty in &SHARE_TYPES {
                    let name = format!("t_{}_{}_{}", pid, i, ty.char());
                    let v = ilp.new_variable(variable().binary(), name.clone());
                    v_vars.insert((t.clone(), *ty), (v, 0.0, name));
                    vars.push(v);
                    // TODO: add constraints for B here
                    let mut x_vec = vec![];
                    for (mid, maps) in mut_maps.get(pid).unwrap().iter() {
                        // buggy?
                        let a_ty = maps.get(t).unwrap();
                        if ty == a_ty {
                            if !b_set.contains_key(&(*pid, t.clone(), *ty)) {
                                b_set.insert((*pid, t.clone(), *ty), Vec::new());
                            }
                            b_set
                                .get_mut(&(*pid, t.clone(), *ty))
                                .unwrap()
                                .push(x_vars.get(&(*pid, *mid)).unwrap().0);
                            x_vec.push(x_vars.get(&(*pid, *mid)).unwrap().0);
                        }
                    }

                    ilp.new_constraint(
                        x_vec
                            .into_iter()
                            .fold((0.0).into(), |acc: Expression, v| acc + v)
                            >> v,
                    );
                }
            }
            _ => {
                if let Some(costs) = costs.get(&t.op) {
                    for (ty, cost) in costs {
                        let name = format!("t_{}_{}_{}", pid, i, ty.char());
                        let v = ilp.new_variable(variable().binary(), name.clone());
                        v_vars.insert((t.clone(), *ty), (v, *cost, name));
                        vars.push(v);
                        // TODO: add constraints for B here
                        let mut x_vec = vec![];
                        for (mid, maps) in mut_maps.get(pid).unwrap().iter() {
                            // buggy?
                            let a_ty = maps.get(t).unwrap();
                            if ty == a_ty {
                                if !b_set.contains_key(&(*pid, t.clone(), *ty)) {
                                    b_set.insert((*pid, t.clone(), *ty), Vec::new());
                                }
                                b_set
                                    .get_mut(&(*pid, t.clone(), *ty))
                                    .unwrap()
                                    .push(x_vars.get(&(*pid, *mid)).unwrap().0);
                                x_vec.push(x_vars.get(&(*pid, *mid)).unwrap().0);
                            }
                        }
                        ilp.new_constraint(
                            x_vec
                                .into_iter()
                                .fold((0.0).into(), |acc: Expression, v| acc + v)
                                >> v,
                        );
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

    // build variables for conversion
    for (def, use_, pid, idx) in &def_uses {
        for from_ty in &SHARE_TYPES {
            for to_ty in &SHARE_TYPES {
                // if def can be from_ty, and use can be to_ty
                if v_vars.contains_key(&(def.clone(), *from_ty))
                    && v_vars.contains_key(&(use_.clone(), *to_ty))
                    && from_ty != to_ty
                {
                    let v = ilp.new_variable(
                        variable().binary(),
                        format!("c_{}_{}_{}2{}", pid, idx, from_ty.char(), to_ty.char()),
                    );
                    e_vars.insert(
                        (def.clone(), *from_ty, *to_ty),
                        (v, *costs.conversions.get(&(*from_ty, *to_ty)).unwrap()),
                    );
                }
            }
        }
    }

    let def_uses: FxHashMap<Term, Vec<Term>> = {
        let mut t = FxHashMap::default();
        for (d, u, _, _) in def_uses {
            t.entry(d).or_insert_with(Vec::new).push(u);
        }
        t
    };

    for (def, uses) in def_uses {
        for use_ in uses {
            for from_ty in &SHARE_TYPES {
                for to_ty in &SHARE_TYPES {
                    e_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                        v_vars.get(&(def.clone(), *from_ty)).map(|t_from| {
                            // c[term i from pi to pi'] >= t[term j with pi'] + t[term i with pi] - 1
                            v_vars
                                .get(&(use_.clone(), *to_ty))
                                .map(|t_to| ilp.new_constraint(c.0 >> (t_from.0 + t_to.0 - 1.0)))
                        })
                    });
                }
            }
        }
    }

    ilp.maximize(
        -e_vars
            .values()
            .map(|(a, b)| (a, b))
            .chain(x_vars.values().map(|(a, b, _)| (a, b)))
            .fold(0.0.into(), |acc: Expression, (v, cost)| acc + *v * *cost),
    );

    let (_opt, solution) = ilp.default_solve().unwrap();

    let mut local_assignments: HashMap<usize, SharingMap> = HashMap::new();

    for (pid, smaps) in mut_maps.iter() {
        for (mid, _maps) in smaps.iter() {
            let name = format!("X_{}_{}", pid, mid);
            if solution.get(&name).unwrap() == &1.0 {
                let map = mut_maps.get(pid).unwrap().get(mid).unwrap().clone();
                local_assignments.insert(*pid, map);
            }
        }
    }

    local_assignments
}

/// Use a ILP to find a optimal combination of mutation assignments
pub fn comb_selection_smart(
    dug: &DefUsesGraph,
    mut_maps: &HashMap<usize, HashMap<usize, SharingMap>>,
    dusg_map: &HashMap<usize, DefUsesSubGraph>,
    cm: &str,
) -> HashMap<usize, SharingMap> {
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
    build_comb_ilp_smart(mut_maps, dug, dusg_map, &costs)
}

/**
 * Combination algo:
 *
 * Notations:
 *  - P ^ i: partitions
 *  - l^i_j: assignment j for P^i
 *  - C^i_j: inner cost (node and inner edges) of P^i with l^i_j
 *  - X^i_j: Assign l^i_j to P^i
 *  - K_{p, p'}: conversion cost from p to p'
 *  - v^i_{k,p}: (edge) vertex k in partition P^i with assignment p
 *  - B^i_{k, p}: Set of indices j such that l^i_j assign p to k
 *  - E_{u, w, p, p'}: cross partition edges that assign u, w with p, p' repsectively
 *
 * Constraints:
 *  - [ for any i, \sum_j X^i_j >= 1 ]: Each partition must have a assignment
 *  - [ for any i,k,  \sum_p v^i_{k, p} >= 1 ]: Each node must have a assignment
 *  - [ E_{u, w, p, p'} >= v{u, p} + v{w, p'} - 1 ]: Edge is added if u and v is assigned with p and p' resp.
 *  
 * Object:
 *  - min[\sum_{i, j} C^i_j X^i_j + \sum E{u,w,p,p'}K_{p, p'}]
 *
 */

fn build_comb_ilp_smart(
    mut_maps: &HashMap<usize, HashMap<usize, SharingMap>>,
    dug: &DefUsesGraph,
    dusg_map: &HashMap<usize, DefUsesSubGraph>,
    costs: &CostModel,
) -> HashMap<usize, SharingMap> {
    // global vars
    let mut ilp = Ilp::new();

    let mut x_vars: FxHashMap<(usize, usize), (Variable, f64, String)> = FxHashMap::default();
    let mut v_vars: FxHashMap<(Term, ShareType), (Variable, f64, String)> = FxHashMap::default();
    let mut e_vars: FxHashMap<(Term, ShareType, ShareType), (Variable, f64)> = FxHashMap::default();

    let mut b_set: FxHashMap<(usize, Term, ShareType), Vec<Variable>> = FxHashMap::default();

    // build variables for selection in each partition X^i_j
    for (pid, smaps) in mut_maps.iter() {
        let mut vars = vec![];
        let du = dusg_map.get(pid).unwrap();
        for (mid, maps) in smaps.iter() {
            let name = format!("X_{}_{}", pid, mid);
            let v = ilp.new_variable(variable().binary(), name.clone());
            // TODO: update this buggy function
            let map_cost = calculate_cost_smart(&maps, costs, du);
            x_vars.insert((*pid, *mid), (v, map_cost, name));
            vars.push(v);
        }
        // Sum of assignment selection is at least 1
        ilp.new_constraint(
            vars.into_iter()
                .fold((0.0).into(), |acc: Expression, v| acc + v)
                >> 1.0,
        );
    }

    //
    // build b set
    // build variables for each edge node v^i_{k,p}
    let mut edge_terms: FxHashSet<(usize, usize, Term)> = FxHashSet::default();
    let mut def_uses: FxHashSet<(Term, Term, usize, usize)> = FxHashSet::default();
    for (pid, du) in dusg_map.iter() {
        let mut index: usize = 1;
        for t in du.ins.clone() {
            edge_terms.insert((*pid, index, t.clone()));
            index = index + 1;
            // get all cross partition egdes:
            for outer_node in dug.use_defs.get(&t).unwrap().iter() {
                def_uses.insert((outer_node.clone(), t.clone(), *pid, index));
            }
        }
        for t in du.outs.clone() {
            edge_terms.insert((*pid, index, t.clone()));
            index = index + 1;
        }
    }

    for (pid, i, t) in edge_terms.iter() {
        let mut vars = vec![];
        match &t.op {
            Op::Var(..) | Op::Const(_) => {
                for ty in &SHARE_TYPES {
                    let name = format!("t_{}_{}_{}", pid, i, ty.char());
                    let v = ilp.new_variable(variable().binary(), name.clone());
                    v_vars.insert((t.clone(), *ty), (v, 0.0, name));
                    vars.push(v);
                    // TODO: add constraints for B here
                    let mut x_vec = vec![];
                    for (mid, maps) in mut_maps.get(pid).unwrap().iter() {
                        // buggy?
                        let a_ty = maps.get(t).unwrap();
                        if ty == a_ty {
                            if !b_set.contains_key(&(*pid, t.clone(), *ty)) {
                                b_set.insert((*pid, t.clone(), *ty), Vec::new());
                            }
                            b_set
                                .get_mut(&(*pid, t.clone(), *ty))
                                .unwrap()
                                .push(x_vars.get(&(*pid, *mid)).unwrap().0);
                            x_vec.push(x_vars.get(&(*pid, *mid)).unwrap().0);
                        }
                    }

                    ilp.new_constraint(
                        x_vec
                            .into_iter()
                            .fold((0.0).into(), |acc: Expression, v| acc + v)
                            >> v,
                    );
                }
            }
            _ => {
                if let Some(costs) = costs.get(&t.op) {
                    for (ty, cost) in costs {
                        let name = format!("t_{}_{}_{}", pid, i, ty.char());
                        let v = ilp.new_variable(variable().binary(), name.clone());
                        v_vars.insert((t.clone(), *ty), (v, *cost, name));
                        vars.push(v);
                        // TODO: add constraints for B here
                        let mut x_vec = vec![];
                        for (mid, maps) in mut_maps.get(pid).unwrap().iter() {
                            // buggy?
                            let a_ty = maps.get(t).unwrap();
                            if ty == a_ty {
                                if !b_set.contains_key(&(*pid, t.clone(), *ty)) {
                                    b_set.insert((*pid, t.clone(), *ty), Vec::new());
                                }
                                b_set
                                    .get_mut(&(*pid, t.clone(), *ty))
                                    .unwrap()
                                    .push(x_vars.get(&(*pid, *mid)).unwrap().0);
                                x_vec.push(x_vars.get(&(*pid, *mid)).unwrap().0);
                            }
                        }
                        ilp.new_constraint(
                            x_vec
                                .into_iter()
                                .fold((0.0).into(), |acc: Expression, v| acc + v)
                                >> v,
                        );
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

    // build variables for conversion
    for (def, use_, pid, idx) in &def_uses {
        for from_ty in &SHARE_TYPES {
            for to_ty in &SHARE_TYPES {
                // if def can be from_ty, and use can be to_ty
                if v_vars.contains_key(&(def.clone(), *from_ty))
                    && v_vars.contains_key(&(use_.clone(), *to_ty))
                    && from_ty != to_ty
                {
                    let v = ilp.new_variable(
                        variable().binary(),
                        format!("c_{}_{}_{}2{}", pid, idx, from_ty.char(), to_ty.char()),
                    );
                    e_vars.insert(
                        (def.clone(), *from_ty, *to_ty),
                        (v, *costs.conversions.get(&(*from_ty, *to_ty)).unwrap()),
                    );
                }
            }
        }
    }

    let def_uses: FxHashMap<Term, Vec<Term>> = {
        let mut t = FxHashMap::default();
        for (d, u, _, _) in def_uses {
            t.entry(d).or_insert_with(Vec::new).push(u);
        }
        t
    };

    for (def, uses) in def_uses {
        for use_ in uses {
            for from_ty in &SHARE_TYPES {
                for to_ty in &SHARE_TYPES {
                    let ilp_version = true;
                    if ilp_version {
                        e_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                            v_vars.get(&(def.clone(), *from_ty)).map(|t_from| {
                                // c[term i from pi to pi'] >= t[term j with pi'] + t[term i with pi] - 1
                                v_vars.get(&(use_.clone(), *to_ty)).map(|t_to| {
                                    ilp.new_constraint(c.0 >> (t_from.0 + t_to.0 - 1.0))
                                })
                            })
                        });
                    } else {
                        // hardcoding here
                        // a2b > y2b
                        // y2a > b2a
                        // a2y > b2y
                        if *from_ty == ShareType::Arithmetic && *to_ty == ShareType::Boolean {
                            let cheap_ty = ShareType::Yao;
                            e_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                v_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    v_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        v_vars.get(&(def.clone(), cheap_ty)).map(|d_ch| {
                                            v_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                                ilp.new_constraint(
                                                    c.0 >> (d_from.0 + u_to.0
                                                        - 1.0
                                                        - d_to.0
                                                        - d_ch.0),
                                                )
                                            })
                                        })
                                    })
                                })
                            });
                        } else if *from_ty == ShareType::Yao && *to_ty == ShareType::Arithmetic {
                            let cheap_ty = ShareType::Boolean;
                            e_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                v_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    v_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        v_vars.get(&(def.clone(), cheap_ty)).map(|d_ch| {
                                            v_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                                ilp.new_constraint(
                                                    c.0 >> (d_from.0 + u_to.0
                                                        - 1.0
                                                        - d_to.0
                                                        - d_ch.0),
                                                )
                                            })
                                        })
                                    })
                                })
                            });
                        } else if *from_ty == ShareType::Arithmetic && *to_ty == ShareType::Yao {
                            let cheap_ty = ShareType::Boolean;
                            e_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                v_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    v_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        v_vars.get(&(def.clone(), cheap_ty)).map(|d_ch| {
                                            v_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                                ilp.new_constraint(
                                                    c.0 >> (d_from.0 + u_to.0
                                                        - 1.0
                                                        - d_to.0
                                                        - d_ch.0),
                                                )
                                            })
                                        })
                                    })
                                })
                            });
                        } else {
                            e_vars.get(&(def.clone(), *from_ty, *to_ty)).map(|c| {
                                v_vars.get(&(def.clone(), *from_ty)).map(|d_from| {
                                    v_vars.get(&(def.clone(), *to_ty)).map(|d_to| {
                                        v_vars.get(&(use_.clone(), *to_ty)).map(|u_to| {
                                            ilp.new_constraint(
                                                c.0 >> (d_from.0 + u_to.0 - 1.0 - d_to.0),
                                            )
                                        })
                                    })
                                })
                            });
                        }
                    }
                }
            }
        }
    }

    ilp.maximize(
        -e_vars
            .values()
            .map(|(a, b)| (a, b))
            .chain(x_vars.values().map(|(a, b, _)| (a, b)))
            .fold(0.0.into(), |acc: Expression, (v, cost)| acc + *v * *cost),
    );

    let (_opt, solution) = ilp.default_solve().unwrap();

    let mut local_assignments: HashMap<usize, SharingMap> = HashMap::new();

    for (pid, smaps) in mut_maps.iter() {
        for (mid, _maps) in smaps.iter() {
            let name = format!("X_{}_{}", pid, mid);
            if solution.get(&name).unwrap() == &1.0 {
                let map = mut_maps.get(pid).unwrap().get(mid).unwrap().clone();
                local_assignments.insert(*pid, map);
            }
        }
    }

    local_assignments
}

/// Calculate the cost of a global assignment
pub fn calculate_cost_smart(smap: &SharingMap, costs: &CostModel, dusg: &DefUsesSubGraph) -> f64 {
    let mut cost: f64 = 0.0;
    let mut conv_cost: HashMap<(Term, ShareType), f64> = HashMap::new();
    for (t, to_ty) in smap {
        match &t.op {
            Op::Var(..)
            | Op::Const(_)
            | Op::BvConcat
            | Op::BvExtract(..)
            | Op::BoolToBv
            | Op::BvBit(_) => {
                cost = cost + 0.0;
            }
            _ => {
                // println!("op: {}", t.op);
                cost = cost + costs.get(&t.op).unwrap().get(to_ty).unwrap();
            }
        }
        for arg_t in dusg.def_uses.get(t).unwrap().iter() {
            if smap.contains_key(&arg_t) {
                let from_ty = smap.get(&arg_t).unwrap();
                if from_ty != to_ty {
                    // todo fix the calculation heres
                    let c = costs.conversions.get(&(*to_ty, *from_ty)).unwrap();
                    conv_cost.insert((t.clone(), *from_ty), *c);
                }
            }
        }
    }
    cost = cost + conv_cost.values().fold(0.0, |acc, &x| acc + x);
    cost
}

/// Calculate the cost of a global assignment
pub fn calculate_cost_smart_dug(smap: &SharingMap, cm: &str, dug: &DefUsesGraph) -> f64 {
    let base_dir = match cm {
        "opa" => "opa",
        "hycc" => "hycc",
        "empirical" => "empirical",
        "empirical_wan" => "empirical_wan",
        _ => panic!("Unknown cost model type: {}", cm),
    };
    let p = format!(
        "{}/third_party/{}/adapted_costs.json",
        var("CARGO_MANIFEST_DIR").expect("Could not find env var CARGO_MANIFEST_DIR"),
        base_dir
    );
    let costs = CostModel::from_opa_cost_file(&p);
    let mut cost: f64 = 0.0;
    let mut conv_cost: HashMap<(Term, ShareType), f64> = HashMap::new();
    for (t, to_ty) in smap {
        match &t.op {
            Op::Var(..)
            | Op::Const(_)
            | Op::BvConcat
            | Op::BvExtract(..)
            | Op::BoolToBv
            | Op::BvBit(_) => {
                cost = cost + 0.0;
            }
            _ => {
                // println!("op: {}", t.op);
                cost = cost + costs.get(&t.op).unwrap().get(to_ty).unwrap();
            }
        }
        for arg_t in dug.def_uses.get(t).unwrap().iter() {
            if smap.contains_key(&arg_t) {
                let from_ty = smap.get(&arg_t).unwrap();
                if from_ty != to_ty {
                    // todo fix the calculation heres
                    let c = costs.conversions.get(&(*to_ty, *from_ty)).unwrap();
                    conv_cost.insert((t.clone(), *from_ty), *c);
                }
            }
        }
    }
    cost = cost + conv_cost.values().fold(0.0, |acc, &x| acc + x);
    cost
}

/// Calculate the cost of a global assignment
pub fn calculate_cost(smap: &SharingMap, costs: &CostModel) -> f64 {
    let mut cost: f64 = 0.0;
    let mut conv_cost: HashMap<(Term, ShareType), f64> = HashMap::new();
    for (t, to_ty) in smap {
        match &t.op {
            Op::Var(..)
            | Op::Const(_)
            | Op::BvConcat
            | Op::BvExtract(..)
            | Op::BoolToBv
            | Op::BvBit(_) => {
                cost = cost + 0.0;
            }
            _ => {
                // println!("op: {}", t.op);
                cost = cost + costs.get(&t.op).unwrap().get(to_ty).unwrap();
            }
        }
        for arg_t in t.cs.iter() {
            if smap.contains_key(&arg_t) {
                let from_ty = smap.get(&arg_t).unwrap();
                if from_ty != to_ty {
                    let c = costs.conversions.get(&(*to_ty, *from_ty)).unwrap();
                    conv_cost.insert((arg_t.clone(), *to_ty), *c);
                }
            }
        }
    }
    cost = cost + conv_cost.values().fold(0.0, |acc, &x| acc + x);
    cost
}




#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_cost_model() {
        let p = format!(
            "{}/third_party/opa/adapted_costs.json",
            var("CARGO_MANIFEST_DIR").expect("Could not find env var CARGO_MANIFEST_DIR")
        );
        let c = CostModel::from_opa_cost_file(&p);
        // random checks from the file...
        assert_eq!(
            &1127.0,
            c.get(&BV_MUL).unwrap().get(&ShareType::Yao).unwrap()
        );
        assert_eq!(
            &1731.0,
            c.get(&BV_MUL).unwrap().get(&ShareType::Boolean).unwrap()
        );
        assert_eq!(
            &7.0,
            c.get(&BV_XOR).unwrap().get(&ShareType::Boolean).unwrap()
        );
    }

    #[test]
    fn mul1_bv_opt() {
        let p = format!(
            "{}/third_party/opa/adapted_costs.json",
            var("CARGO_MANIFEST_DIR").expect("Could not find env var CARGO_MANIFEST_DIR")
        );
        let costs = CostModel::from_opa_cost_file(&p);
        let cs = Computation {
            outputs: vec![term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("b".to_owned(), Sort::BitVector(32)))
            ]],
            metadata: ComputationMetadata::default(),
            precomputes: Default::default(),
        };
        let cg = cs.to_cs();
        let _assignment = build_ilp(&cg, &costs);
    }

    #[test]
    fn huge_mul_then_eq() {
        let p = format!(
            "{}/third_party/opa/adapted_costs.json",
            var("CARGO_MANIFEST_DIR").expect("Could not find env var CARGO_MANIFEST_DIR")
        );
        let costs = CostModel::from_opa_cost_file(&p);
        let cs = Computation {
            outputs: vec![term![Op::Eq;
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32)))
            ]
            ]
            ]
            ]
            ]
            ]
            ],
            leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32)))
            ]],
            metadata: ComputationMetadata::default(),
            precomputes: Default::default(),
        };
        let cg = cs.to_cs();
        let assignment = build_ilp(&cg, &costs);
        // Big enough to do the math with arith
        assert_eq!(
            &ShareType::Arithmetic,
            assignment.get(&cs.outputs[0].cs[0]).unwrap()
        );
        // Then convert to boolean
        assert_eq!(&ShareType::Boolean, assignment.get(&cs.outputs[0]).unwrap());
    }

    #[test]
    fn big_mul_then_eq() {
        let p = format!(
            "{}/third_party/opa/adapted_costs.json",
            var("CARGO_MANIFEST_DIR").expect("Could not find env var CARGO_MANIFEST_DIR")
        );
        let costs = CostModel::from_opa_cost_file(&p);
        let cs = Computation {
            outputs: vec![term![Op::Eq;
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32)))
            ]
            ]
            ]
            ],
            leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32)))
            ]],
            metadata: ComputationMetadata::default(),
            precomputes: Default::default(),
        };
        let cg = cs.to_cs();
        let assignment = build_ilp(&cg, &costs);
        // All yao
        assert_eq!(
            &ShareType::Yao,
            assignment.get(&cs.outputs[0].cs[0]).unwrap()
        );
        assert_eq!(&ShareType::Yao, assignment.get(&cs.outputs[0]).unwrap());
    }
}
