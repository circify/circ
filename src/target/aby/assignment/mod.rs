//! Machinery for assigning operations to sharing schemes
use crate::ir::term::*;
use fxhash::FxHashMap;
use serde_json::Value;
use std::{env::var, fs::File, path::Path};

pub mod def_uses;
#[cfg(feature = "lp")]
pub mod ilp;
pub mod ilp_opa;

/// The sharing scheme used for an operation
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum ShareType {
    /// Arithmetic sharing (additive mod `Z_(2^l)`)
    Arithmetic,
    /// Boolean sharing (additive mod `Z_2`)
    Boolean,
    /// Yao sharing (one party holds `k_a`, `k_b`, other knows the `{k_a, k_b} <-> {0, 1}` mapping)
    Yao,
    /// None type, reserved for terms without circuit representation
    None,
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
            ShareType::None => 'n',
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
    pub conversions: FxHashMap<(ShareType, ShareType), f64>,

    /// Operator costs: maps (op, type) to cost
    pub ops: FxHashMap<String, FxHashMap<ShareType, f64>>,

    /// Zero costs
    pub zero: FxHashMap<ShareType, f64>,
}

impl CostModel {
    /// Cost model constructor
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
            zero,
        }
    }

    /// Create a cost model from an OPA json file, like [this](https://github.com/ishaq/OPA/blob/d613c15ff715fa62c03e37b673548f94c16bfe0d/solver/sample-costs.json)
    pub fn from_opa_cost_file(p: &impl AsRef<Path>, k: FxHashMap<String, f64>) -> CostModel {
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
        let get_depth =
            |share_type: &str, obj: &serde_json::map::Map<String, Value>| -> Option<f64> {
                let o = obj
                    .get("depth")
                    .unwrap_or_else(|| panic!("Missing {} in {:#?}", "depth", obj));
                Some(
                    o.get(share_type)
                        .unwrap_or_else(|| panic!("Missing {} entry in {:#?}", share_type, o))
                        .as_f64()
                        .expect("not a number"),
                )
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
            if !op_name.contains('2') && !op_name.contains("depth") {
                for (share_type, share_name) in &[(Arithmetic, "a"), (Boolean, "b"), (Yao, "y")] {
                    if let Some(c) = get_cost_opt(share_name, cost.as_object().unwrap()) {
                        let mut cost_depth: f64 = 0.0;
                        if *share_type != Yao {
                            if let Some(d) = get_depth(share_name, cost.as_object().unwrap()) {
                                cost_depth += k.get(share_name.clone()).unwrap_or_else(|| &1.0)
                                    * d
                                    * get_depth(share_name, costs).unwrap();
                            }
                        }
                        ops.entry(op_name.clone())
                            .or_insert_with(FxHashMap::default)
                            .insert(*share_type, c + cost_depth);
                        // println!("Insert cost model:{}, {}, {}", op_name, share_name, c + cost_depth);
                    }
                }
            }
        }
        CostModel::new(conversions, ops)
    }
}

pub fn get_cost_model(cm: &str) -> CostModel {
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
    CostModel::from_opa_cost_file(&p, FxHashMap::default())
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
                    if let Some(costs) = cost_model.ops.get(&term.op().to_string()) {
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
                    if let Some(costs) = cost_model.ops.get(&term.op().to_string()) {
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
                    if let Some(costs) = cost_model.ops.get(&term.op().to_string()) {
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
