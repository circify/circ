//! # Tuple elimination pass
//!
//! Elimates tuple-related terms.
//!
//! The idea is to do a bottom-up pass mapping all terms to tuple-free trees of terms.
//!
//!    * Tuple variables are suffixed. `x: (bool, bool)` becomes `x.0: bool, x.1: bool`.
//!    * Tuple constants are replaced with trees
//!    * Tuple constructors make trees
//!    * Tuple accesses open up trees
//!    * Tuple ITEs yield trees of ITEs
//!    * Tuple EQs yield conjunctions of EQs

use std::rc::Rc;

use crate::ir::term::{
    check, leaf_term, term, BoolNaryOp, Constraints, Op, PostOrderIter, Sort, Term, TermMap, Value,
};

type Tree = Rc<TreeData>;

#[derive(Clone, Debug)]
enum TreeData {
    Leaf(Term),
    Tuple(Vec<Tree>),
}

impl TreeData {
    fn unwrap_leaf(&self) -> &Term {
        match self {
            TreeData::Leaf(l) => l,
            d => panic!("expected leaf, got {:?}", d),
        }
    }
    fn unwrap_tuple(&self) -> &Vec<Tree> {
        match self {
            TreeData::Tuple(l) => l,
            d => panic!("expected tuple, got {:?}", d),
        }
    }
    fn unfold_tuple_into(&self, terms: &mut Vec<Term>) {
        match self {
            TreeData::Leaf(l) => terms.push(l.clone()),
            TreeData::Tuple(l) => l.iter().for_each(|x| x.unfold_tuple_into(terms)),
        }
    }
    fn unfold_tuple(&self) -> Vec<Term> {
        let mut terms = Vec::new();
        self.unfold_tuple_into(&mut terms);
        terms
    }
    fn from_value(v: Value) -> TreeData {
        match v {
            Value::Tuple(vs) => {
                TreeData::Tuple(vs.into_iter().map(Self::from_value).map(Rc::new).collect())
            }
            v => TreeData::Leaf(leaf_term(Op::Const(v))),
        }
    }
}

fn restructure(sort: &Sort, items: &mut impl Iterator<Item = Term>) -> Tree {
    if let Sort::Tuple(sorts) = sort {
        Rc::new(TreeData::Tuple(
            sorts.iter().map(|c| restructure(c, items)).collect(),
        ))
    } else {
        Rc::new(TreeData::Leaf(
            items
                .next()
                .unwrap_or_else(|| panic!("No term when building {}", sort)),
        ))
    }
}

struct Pass {
    map: TermMap<Tree>,
    cs: Constraints,
}

impl Pass {
    fn new(cs: Constraints) -> Self {
        Self {
            map: TermMap::new(),
            cs,
        }
    }

    #[track_caller]
    fn get_tree(&self, t: &Term) -> &Tree {
        self.map
            .get(t)
            .unwrap_or_else(|| panic!("missing tree for term: {} in {:?}", t, self.map))
    }

    fn create_vars(
        &mut self,
        prefix: &str,
        sort: &Sort,
        value: Option<Value>,
        public: bool,
    ) -> Tree {
        match sort {
            Sort::Tuple(sorts) => {
                let mut values = value.map(|v| match v {
                    Value::Tuple(t) => t,
                    _ => panic!(),
                });
                Rc::new(TreeData::Tuple(
                    sorts
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| {
                            self.create_vars(
                                &format!("{}.{}", prefix, i),
                                sort,
                                values
                                    .as_mut()
                                    .map(|v| std::mem::replace(&mut v[i], Value::Bool(true))),
                                public,
                            )
                        })
                        .collect(),
                ))
            }
            _ => Rc::new(TreeData::Leaf(
                if self.cs.public_inputs.contains(prefix)
                    && self
                        .cs
                        .values
                        .as_ref()
                        .map(|v| v.contains_key(prefix))
                        .unwrap_or(false)
                {
                    leaf_term(Op::Var(prefix.into(), sort.clone()))
                } else {
                    self.cs
                        .new_var(prefix, sort.clone(), || value.unwrap().clone(), public)
                },
            )),
        }
    }

    fn embed_step(&mut self, t: &Term) {
        let s = check(t);
        let tree = if let Sort::Tuple(_) = s {
            match &t.op {
                Op::Const(v) => Rc::new(TreeData::from_value(v.clone())),
                Op::Var(name, sort) => {
                    let public = self.cs.public_inputs.contains(name);
                    self.create_vars(
                        name,
                        sort,
                        self.cs
                            .values
                            .as_ref()
                            .map(|v| v.get(name).unwrap().clone()),
                        public,
                    )
                }
                Op::Tuple => Rc::new(TreeData::Tuple(
                    t.cs.iter().map(|c| self.get_tree(c).clone()).collect(),
                )),
                Op::Ite => {
                    let cond = self.get_tree(&t.cs[0]).unwrap_leaf();
                    let trues = self.get_tree(&t.cs[1]).unfold_tuple();
                    let falses = self.get_tree(&t.cs[2]).unfold_tuple();
                    restructure(
                        &s,
                        &mut trues
                            .into_iter()
                            .zip(falses.into_iter())
                            .map(|(a, b)| term![Op::Ite; cond.clone(), a, b]),
                    )
                }
                Op::Field(i) => self.get_tree(&t.cs[0]).unwrap_tuple()[*i].clone(),
                o => panic!("Bad tuple operator: {}", o),
            }
        } else {
            match &t.op {
                Op::Field(i) => self.get_tree(&t.cs[0]).unwrap_tuple()[*i].clone(),
                Op::Eq => {
                    let c_sort = check(&t.cs[0]);
                    Rc::new(TreeData::Leaf(if let Sort::Tuple(_) = c_sort {
                        let xs = self.get_tree(&t.cs[0]).unfold_tuple();
                        let ys = self.get_tree(&t.cs[1]).unfold_tuple();
                        term(
                            Op::BoolNaryOp(BoolNaryOp::And),
                            xs.into_iter()
                                .zip(ys.into_iter())
                                .map(|(x, y)| term![Op::Eq; x, y])
                                .collect(),
                        )
                    } else {
                        term(
                            t.op.clone(),
                            t.cs.iter()
                                .map(|c| self.get_tree(c).unwrap_leaf().clone())
                                .collect(),
                        )
                    }))
                }
                _ => Rc::new(TreeData::Leaf(term(
                    t.op.clone(),
                    t.cs.iter()
                        .map(|c| self.get_tree(c).unwrap_leaf().clone())
                        .collect(),
                ))),
            }
        };
        if let TreeData::Leaf(t) = &*tree {
            debug_assert!(tuple_free(t.clone()), "Tuple in {:?}", tree);
        }
        self.map.insert(t.clone(), tree);
    }

    fn embed(&mut self, t: &Term) -> Tree {
        for c in PostOrderIter::new(t.clone()) {
            self.embed_step(&c);
        }
        self.get_tree(t).clone()
    }
}

fn tuple_free(t: Term) -> bool {
    !PostOrderIter::new(t).any(|c| match check(&c) {
        Sort::Tuple(_) => true,
        _ => false,
    })
}

/// Run the tuple elimination pass.
pub fn eliminate_tuples(mut cs: Constraints) -> Constraints {
    let assertions = std::mem::take(&mut cs.assertions);
    let conj = term(Op::BoolNaryOp(BoolNaryOp::And), assertions);
    let mut pass = Pass::new(cs);
    pass.embed(&conj);
    let new_assertions: Vec<Term> = conj
        .cs
        .iter()
        .map(|c| pass.get_tree(c).unwrap_leaf().clone())
        .collect();
    pass.cs.assertions = new_assertions;
    pass.cs
}
