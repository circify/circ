//! Machinery for assigning operations to sharing schemes
use crate::ir::term::*;
use fxhash::FxHashMap;
use serde_json::Value;
use std::{env::var, fs::File, path::Path};

#[cfg(feature = "lp")]
pub mod ilp;

/// The sharing scheme used for an operation
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum ShareType {
    /// Arithmetic sharing (additive mod `Z_(2^l)`)
    Arithmetic,
    /// Boolean sharing (additive mod `Z_2`)
    Boolean,
    /// Yao sharing (one party holds `k_a`, `k_b`, other knows the `{k_a, k_b} <-> {0, 1}` mapping)
    Yao,
}

/// List of share types.
pub const SHARE_TYPES: [ShareType; 3] = [ShareType::Arithmetic, ShareType::Boolean, ShareType::Yao];

impl ShareType {
    /// Output associated char for each ShareType
    pub fn char(&self) -> char {
        match self {
            ShareType::Arithmetic => 'a',
            ShareType::Boolean => 'b',
            ShareType::Yao => 'y',
        }
    }
}

/// A map from terms (operations or inputs) to sharing schemes they use
pub type SharingMap = TermMap<ShareType>;

/// A cost model for ABY operations and share conversions
#[derive(Debug)]
pub struct CostModel {
    #[allow(dead_code)]
    /// Conversion costs: maps (from, to) pairs to cost
    conversions: FxHashMap<(ShareType, ShareType), f64>,

    /// Operator costs: maps (op, type) to cost
    ops: FxHashMap<String, FxHashMap<ShareType, f64>>,

    /// Zero costs
    zero: FxHashMap<ShareType, f64>,
}

impl CostModel {
    pub fn new(
        conversions: FxHashMap<(ShareType, ShareType), f64>,
        ops: FxHashMap<String, FxHashMap<ShareType, f64>>,
    ) -> CostModel {
        let mut zero: FxHashMap<ShareType, f64> = FxHashMap::default();
        zero.insert(ShareType::Arithmetic, 0.0);
        zero.insert(ShareType::Boolean, 0.0);
        zero.insert(ShareType::Yao, 0.0);
        CostModel {
            conversions,
            ops,
            zero: zero,
        }
    }

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

        for (op_name, cost) in costs {
            // HACK: assumes the presence of 2 partitions names into conversion and otherwise.
            if !op_name.contains('2') {
                for (share_type, share_name) in &[(Arithmetic, "a"), (Boolean, "b"), (Yao, "y")] {
                    if let Some(c) = get_cost_opt(share_name, cost.as_object().unwrap()) {
                        ops.entry(op_name.clone())
                            .or_insert_with(FxHashMap::default)
                            .insert(*share_type, c);
                    }
                }
            }
        }
        CostModel::new(conversions, ops)
    }

    fn get(&self, op: &Op) -> Option<&FxHashMap<ShareType, f64>> {
        match op {
            Op::Field(_) | Op::Call(..) | Op::Update(..) => Some(&self.zero),
            _ => {
                let op_name = match op.clone() {
                    // assume comparisions are unsigned
                    BV_UGE => "ge",
                    BV_ULE => "le",
                    BV_UGT => "gt",
                    BV_ULT => "lt",
                    // assume n-ary ops apply to BVs
                    BV_ADD => "add",
                    BV_MUL => "mul",
                    BV_AND => "and",
                    BV_OR => "or",
                    BV_XOR => "xor",
                    Op::Eq => "eq",
                    // assume not operator is for not equals
                    Op::Not => "ne",
                    BV_SHL => "shl",
                    // assume shr is logical, not arithmetic
                    BV_LSHR => "shr",
                    BV_SUB => "sub",
                    ITE => "mux",
                    BV_UDIV => "div",
                    BV_UREM => "rem",
                    // added to pass test case
                    AND => "&&",
                    OR => "||",
                    _ => panic!("Unknown operator: {:#?}", op),
                };

                self.ops.get(op_name)
            }
        }
    }
}

fn get_cost_model(cm: &str) -> CostModel {
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
    CostModel::from_opa_cost_file(&p)
}

/// Assigns boolean sharing to all terms
pub fn assign_all_boolean(c: &Computation, _cm: &str) -> SharingMap {
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| (term, ShareType::Boolean))
        })
        .collect()
}

/// Assigns Yao sharing to all terms
pub fn assign_all_yao(c: &Computation, _cm: &str) -> SharingMap {
    c.outputs
        .iter()
        .flat_map(|output| PostOrderIter::new(output.clone()).map(|term| (term, ShareType::Yao)))
        .collect()
}

/// Assign greedy Arithmetic and Boolean sharings based on cost model
pub fn assign_arithmetic_and_boolean(c: &Computation, cm: &str) -> SharingMap {
    let cost_model = get_cost_model(cm);
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| {
                (
                    term.clone(),
                    if let Some(costs) = cost_model.get(&term.op) {
                        let mut min_ty: ShareType = ShareType::Boolean;
                        let mut min_cost: f64 = costs[&min_ty];
                        for ty in &[ShareType::Arithmetic] {
                            if let Some(c) = costs.get(ty) {
                                if *c < min_cost {
                                    min_ty = *ty;
                                    min_cost = *c;
                                }
                            }
                        }
                        min_ty
                    } else {
                        ShareType::Boolean
                    },
                )
            })
        })
        .collect()
}

/// Assign greedy Arithmetic and yao sharings based on cost model
pub fn assign_arithmetic_and_yao(c: &Computation, cm: &str) -> SharingMap {
    let cost_model = get_cost_model(cm);
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| {
                (
                    term.clone(),
                    if let Some(costs) = cost_model.get(&term.op) {
                        let mut min_ty: ShareType = ShareType::Yao;
                        let mut min_cost: f64 = costs[&min_ty];
                        for ty in &[ShareType::Arithmetic] {
                            if let Some(c) = costs.get(ty) {
                                if *c < min_cost {
                                    min_ty = *ty;
                                    min_cost = *c;
                                }
                            }
                        }
                        min_ty
                    } else {
                        ShareType::Yao
                    },
                )
            })
        })
        .collect()
}

/// Assign all greedy sharings based on cost model
pub fn assign_greedy(c: &Computation, cm: &str) -> SharingMap {
    let cost_model = get_cost_model(cm);
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| {
                (
                    term.clone(),
                    if let Some(costs) = cost_model.get(&term.op) {
                        let mut min_ty: ShareType = ShareType::Yao;
                        let mut min_cost: f64 = costs[&min_ty];
                        for ty in &[ShareType::Arithmetic, ShareType::Boolean] {
                            if let Some(c) = costs.get(ty) {
                                if *c < min_cost {
                                    min_ty = *ty;
                                    min_cost = *c;
                                }
                            }
                        }
                        min_ty
                    } else {
                        ShareType::Boolean
                    },
                )
            })
        })
        .collect()
}
