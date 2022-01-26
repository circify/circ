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
use serde_json::Value;

use super::{ShareType, SharingMap, SHARE_TYPES};
use crate::ir::term::*;

use crate::target::ilp::{variable, Expression, Ilp, Variable};

use std::{env::var, fs::File, path::Path};

/// A cost model for ABY operations and share conversions
#[derive(Debug)]
pub struct CostModel {
    /// Conversion costs: maps (from, to) pairs to cost
    conversions: FxHashMap<(ShareType, ShareType), f64>,

    /// Operator costs: maps (op, type) to cost
    ops: FxHashMap<Op, FxHashMap<ShareType, f64>>,
}

impl CostModel {
    /// Create a cost model from an OPA json file, like [this](https://github.com/ishaq/OPA/blob/d613c15ff715fa62c03e37b673548f94c16bfe0d/solver/sample-costs.json)
    pub fn from_opa_cost_file(p: &impl AsRef<Path>) -> CostModel {
        use ShareType::*;
        let get_cost_opt =
            |share_name: &str, obj: &serde_json::map::Map<String, Value>| -> Option<f64> {
                let o = obj.get(share_name)?;
                Some(
                    o.get("32")
                        .unwrap_or_else(|| panic!("Missing op '32' entry in {:#?}", o))
                        .as_f64()
                        .expect("not a number"),
                )
            };
        let get_cost = |op_name: &str, obj: &serde_json::map::Map<String, Value>| -> f64 {
            let o = obj
                .get(op_name)
                .unwrap_or_else(|| panic!("Missing op {} in {:#?}", op_name, obj));
            Some(
                o.get("32")
                    .unwrap_or_else(|| panic!("Missing op '32' entry in {:#?}", o))
                    .as_f64()
                    .expect("not a number"),
            )
            .unwrap()
        };
        let mut conversions = FxHashMap::default();
        let mut ops = FxHashMap::default();
        let f = File::open(p).expect("Missing file");
        let json: Value = serde_json::from_reader(f).expect("Bad JSON");
        let costs = json.as_object().unwrap();
        // conversions
        conversions.insert((Arithmetic, Boolean), get_cost("a2b", costs));
        conversions.insert((Boolean, Arithmetic), get_cost("b2a", costs));
        conversions.insert((Yao, Boolean), get_cost("y2b", costs));
        conversions.insert((Boolean, Yao), get_cost("b2y", costs));
        conversions.insert((Yao, Arithmetic), get_cost("y2a", costs));
        conversions.insert((Arithmetic, Yao), get_cost("a2y", costs));

        let ops_from_name = |name: &str| {
            match name {
                // assume comparisions are unsigned
                "ge" => vec![BV_UGE],
                "le" => vec![BV_ULE],
                "gt" => vec![BV_UGT],
                "lt" => vec![BV_ULT],
                // assume n-ary ops apply to BVs
                "add" => vec![BV_ADD],
                "mul" => vec![BV_MUL],
                "and" => vec![BV_AND],
                "or" => vec![BV_OR],
                "xor" => vec![BV_XOR],
                // assume eq applies to BVs
                "eq" => vec![Op::Eq],
                "shl" => vec![BV_SHL],
                // assume shr is logical, not arithmetic
                "shr" => vec![BV_LSHR],
                "sub" => vec![BV_SUB],
                "mux" => vec![ITE],
                "ne" => vec![Op::Not, Op::Eq],
                "div" => vec![BV_UDIV],
                "rem" => vec![BV_UREM],
                // added to pass test case
                "&&" => vec![AND],
                "||" => vec![OR],
                _ => panic!("Unknown operator name: {}", name),
            }
        };
        for (op_name, cost) in costs {
            // HACK: assumes the presence of 2 partitions names into conversion and otherwise.
            if !op_name.contains('2') {
                for op in ops_from_name(op_name) {
                    for (share_type, share_name) in &[(Arithmetic, "a"), (Boolean, "b"), (Yao, "y")]
                    {
                        if let Some(c) = get_cost_opt(share_name, cost.as_object().unwrap()) {
                            ops.entry(op.clone())
                                .or_insert_with(FxHashMap::default)
                                .insert(*share_type, c);
                        }
                    }
                }
            }
        }
        CostModel { conversions, ops }
    }
}

/// Uses an ILP to assign...
pub fn assign(c: &Computation, cm: &str) -> SharingMap {
    let base_dir = match cm {
        "opa" => "opa",
        "hycc" => "hycc",
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

fn build_ilp(c: &Computation, costs: &CostModel) -> SharingMap {
    let mut terms: TermSet = TermSet::new();
    let mut def_uses: FxHashSet<(Term, Term)> = FxHashSet::default();
    for o in &c.outputs {
        for t in PostOrderIter::new(o.clone()) {
            terms.insert(t.clone());
            for c in &t.cs {
                def_uses.insert((c.clone(), t.clone()));
            }
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
                if let Some(costs) = costs.ops.get(&t.op) {
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
            c.ops.get(&BV_MUL).unwrap().get(&ShareType::Yao).unwrap()
        );
        assert_eq!(
            &1731.0,
            c.ops
                .get(&BV_MUL)
                .unwrap()
                .get(&ShareType::Boolean)
                .unwrap()
        );
        assert_eq!(
            &7.0,
            c.ops
                .get(&BV_XOR)
                .unwrap()
                .get(&ShareType::Boolean)
                .unwrap()
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
            values: None,
        };
        let _assignment = build_ilp(&cs, &costs);
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
            values: None,
        };
        let assignment = build_ilp(&cs, &costs);
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
            values: None,
        };
        let assignment = build_ilp(&cs, &costs);
        // All yao
        assert_eq!(
            &ShareType::Yao,
            assignment.get(&cs.outputs[0].cs[0]).unwrap()
        );
        assert_eq!(&ShareType::Yao, assignment.get(&cs.outputs[0]).unwrap());
    }
}
