//! A general-purpose RAM extractor
use super::*;

use fxhash::FxHashMap as HashMap;
use fxhash::FxHashSet as HashSet;
use std::collections::BinaryHeap;

use log::{debug, trace};

/// Graph of the *arrays* in the computation.
///
/// Nodes are *most* of the array-sorted terms (see "subsumed store" for the exception).
///
/// Edges go from dependent arrays to their dependencies and represent stores,
/// ITEs, and conditional stores.
///
/// A conditional store has form T = (ite C (store A I V) A).
///
/// It is regarded as a single edge from T to A, so long as the interior store
/// (store A I V) has no other dependents. In this case, the interior store is
/// called a "subsumed store", and is not part of the array graph itself.
///
/// The "constant-free" graph has constant arrays removed.
///
/// An array term in the graph is non-RAM if is is connected (undirectedly) in
/// the constant-free graph to any node with multiple parents or children in the
/// constant-free graph.
///
#[derive(Debug)]
struct ArrayGraph {
    /// Map from array terms to their children (dependencies)
    children: TermMap<Vec<Term>>,
    /// Set of RAM array terms (includes all ram leaves).
    ram_terms: TermSet,
}

/// Are terms of sort `s` hashable using a UHF keyed by field type `f`.
fn hashable(s: &Sort, f: &FieldT) -> bool {
    match s {
        Sort::Field(ff) => f == ff,
        Sort::Tuple(ss) => ss.iter().all(|s| hashable(s, f)),
        Sort::BitVector(_) => true,
        Sort::Bool => true,
        Sort::Array(_k, v, size) => *size < 20 && hashable(v, f),
        _ => false,
    }
}

/// Does this array have a sort compatible with our RAM machinery?
fn right_sort(t: &Term, f: &FieldT) -> bool {
    let s = check(t);
    if let Sort::Array(k, v, _) = &s {
        if let Sort::Field(k) = &**k {
            k == f && hashable(v, f)
        } else {
            false
        }
    } else {
        false
    }
}

/// Does this term create an array from non-arrays?
/// (or lower-rank arrays)
fn array_leaf(a: &Term) -> bool {
    matches!(a.op(), Op::Fill(..) | Op::Const(..) | Op::Array(..))
}

impl ArrayGraph {
    fn new(c: &Computation, field: &FieldT) -> Self {
        let mut ps = TermMap::default();
        let mut cs = TermMap::default();
        let mut arrs = TermSet::default();

        // locate all array terms
        for t in c.terms_postorder() {
            if check(&t).is_array() {
                arrs.insert(t.clone());
                cs.insert(t.clone(), Vec::new());
                ps.insert(t, Vec::new());
            }
        }

        // compute parents and children
        for t in c.terms_postorder() {
            if check(&t).is_array() {
                for c in t.cs() {
                    if check(c).is_array() {
                        cs.get_mut(&t).unwrap().push(c.clone());
                        ps.get_mut(c).unwrap().push(t.clone());
                    }
                }
            }
        }

        let mut ram_terms: TermSet = TermSet::default();
        // first, we grow the set of RAM terms, from leaves towards dependents.
        {
            // we start with the explicitly marked RAMs
            trace!("Starting with {} RAMs", c.ram_arrays.len());
            let mut stack: Vec<Term> = c
                .ram_arrays
                .iter()
                .filter(|a| arrs.contains(a))
                .cloned()
                .collect();
            while let Some(top) = stack.pop() {
                if ram_terms.insert(top.clone()) {
                    trace!("Maybe RAM: {}", top);
                    for p in ps.get(&top).unwrap() {
                        if right_sort(p, field) {
                            stack.push(p.clone());
                        }
                    }
                }
            }
        }

        // now, we prune any term connected to a non-leaf with multiple parents.
        {
            // initial non-RAM terms
            let mut stack: Vec<Term> = ram_terms
                .iter()
                .filter(|a| {
                    !array_leaf(a) && (ps.get(a).unwrap().len() > 1 || cs.get(a).unwrap().len() > 1)
                })
                .cloned()
                .collect();
            // Now, propagate
            while let Some(t) = stack.pop() {
                if !array_leaf(&t) && ram_terms.contains(&t) {
                    trace!("Non-RAM: {}", t);
                    ram_terms.remove(&t);
                    for t in ps.get(&t).into_iter().flatten() {
                        stack.push(t.clone());
                    }
                    for t in cs.get(&t).into_iter().flatten() {
                        stack.push(t.clone());
                    }
                }
            }
        }
        Self {
            children: cs,
            ram_terms,
        }
    }
}

#[derive(Debug)]
struct Extactor {
    rams: Vec<Ram>,
    term_ram: TermMap<RamId>,
    read_terms: TermMap<Term>,
    graph: ArrayGraph,
    cfg: AccessCfg,
}

type RamId = usize;

impl Extactor {
    fn new(c: &Computation, cfg: AccessCfg) -> Self {
        let graph = ArrayGraph::new(c, &cfg.field);
        Self {
            rams: Vec::new(),
            term_ram: TermMap::default(),
            read_terms: TermMap::default(),
            cfg,
            graph,
        }
    }
    /// Given a RAM leaf, create a new RAM, and return its id.
    /// For a non-leaf, lookup and existing id.
    fn get_or_start(&mut self, t: &Term) -> RamId {
        if array_leaf(t) {
            self.start_ram_for_leaf(t)
        } else {
            *self.term_ram.get(t).unwrap()
        }
    }

    /// Given a RAM leaf, create a new RAM.
    fn start_ram_for_leaf(&mut self, t: &Term) -> RamId {
        assert!(array_leaf(t));

        // create a default RAM from `t`'s sort.
        let id = self.rams.len();
        let t_sort = check(t);
        let (key_sort, val_sort, size) = t_sort.as_array();
        let def = BoundaryConditions::Default(key_sort.default_term());
        let mut ram = Ram::new(id, size, self.cfg.clone(), val_sort.clone(), def);

        // update with details specific to `t`.
        match &t.op() {
            Op::Fill(..) => {
                // for fill: set default value
                let value = &t.cs()[0];
                ram.boundary_conditions = BoundaryConditions::Default(value.clone());
            }
            Op::Const(Value::Array(a)) => {
                // for a constant: add (constant) writes
                for (k, v) in &a.map {
                    ram.new_write(
                        leaf_term(Op::Const(k.clone())),
                        leaf_term(Op::Const(v.clone())),
                        self.cfg.true_.clone(),
                    );
                }
            }
            Op::Array(..) => {
                // for an array constructor: add writes (at constant indices)
                for (i, val) in t.cs().iter().enumerate() {
                    ram.new_write(key_sort.nth_elem(i), val.clone(), bool_lit(true));
                }
            }
            o => panic!("Non-RAM-leaf: {}", o),
        }
        self.rams.push(ram);
        id
    }
}

/// Given a set of terms, return an ordering of them in post-order, but also with array selects on
/// A before stores to A.
fn array_order<'a>(terms: HashSet<&'a Term>) -> Vec<&'a Term> {
    let mut parents: HashMap<&'a Term, HashSet<&'a Term>> = Default::default();
    let mut children: HashMap<&'a Term, HashSet<&'a Term>> = Default::default();
    for t in &terms {
        parents.entry(t).or_default();
        children.entry(t).or_default();
        for c in t.cs() {
            debug_assert!(terms.contains(c));
            parents.entry(c).or_default().insert(t);
            children.entry(t).or_default().insert(c);
        }
    }
    let mut output: Vec<&'a Term> = Default::default();
    // max-heap contains (is_select, term) pairs; so, selects go first.
    let mut to_output: BinaryHeap<(bool, &'a Term)> = terms
        .iter()
        .filter(|t| t.cs().is_empty())
        .map(|t| (false, *t))
        .collect();
    let mut children_not_outputted: HashMap<&'a Term, usize> = children
        .iter()
        .map(|(term, children)| (*term, children.len()))
        .collect();
    while let Some((_, output_me)) = to_output.pop() {
        output.push(output_me);
        for p in parents.get(&output_me).unwrap() {
            let count = children_not_outputted.get_mut(p).unwrap();
            assert!(*count > 0);
            *count -= 1;
            if *count == 0 {
                to_output.push((matches!(p.op(), Op::Select), *p));
            }
        }
    }
    assert_eq!(output.len(), terms.len());
    output
}

impl RewritePass for Extactor {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        t: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        // First, we rewrite RAM terms.
        if self.graph.ram_terms.contains(t) && !array_leaf(t) {
            // Since this is a RAM non-leaf, it is a (c)store.
            assert!(
                matches!(t.op(), Op::Store | Op::CStore),
                "Bad ram term: {}",
                t
            );
            debug_assert!(self.graph.children.get(t).is_some());
            debug_assert_eq!(1, self.graph.children.get(t).unwrap().len());
            // Get dependency's RAM
            let child = self.graph.children.get(t).unwrap()[0].clone();
            let ram_id = self.get_or_start(&child);
            let ram = &mut self.rams[ram_id];
            // Build new term, and parse as a c-store
            let new = term(t.op().clone(), rewritten_children());
            match new.op() {
                Op::Store => {
                    ram.new_write(new.cs()[1].clone(), new.cs()[2].clone(), bool_lit(true));
                }
                Op::CStore => {
                    ram.new_write(
                        new.cs()[1].clone(),
                        new.cs()[2].clone(),
                        new.cs()[3].clone(),
                    );
                }
                o => unreachable!("Non-RAM operator: {}", o),
            };
            // Add the write to the RAM
            let id = ram.id;
            self.term_ram.insert(t.clone(), id);
            None
        } else {
            match &t.op() {
                // Rewrite select's whose array is a RAM term
                Op::Select if self.graph.ram_terms.contains(&t.cs()[0]) => {
                    let array = &t.cs()[0];
                    let idx = &t.cs()[1];
                    // If we're based on a leaf
                    let ram_id = if array_leaf(array) {
                        // check if that leaf has a RAM already
                        if let Some(id) = self.term_ram.get(array) {
                            *id
                        } else {
                            let id = self.start_ram_for_leaf(array);

                            self.term_ram.insert(array.clone(), id);
                            id
                        }
                    } else {
                        // otherwise, assume that our parent has a RAM already
                        *self.term_ram.get(array).unwrap()
                    };
                    let ram = &mut self.rams[ram_id];
                    let read_value = ram.new_read(idx.clone(), computation, t.clone());
                    self.read_terms.insert(t.clone(), read_value.clone());
                    Some(read_value)
                }
                _ => None,
            }
        }
    }

    fn traverse(&mut self, computation: &mut Computation) {
        let terms: Vec<Term> = computation.terms_postorder().collect();
        let term_refs: HashSet<&Term> = terms.iter().collect();
        let mut cache = TermMap::<Term>::default();
        for top in array_order(term_refs) {
            debug_assert!(!cache.contains_key(top));
            let new_t_opt = self.visit_cache(computation, top, &cache);
            let new_t = new_t_opt.unwrap_or_else(|| {
                term(
                    top.op().clone(),
                    top.cs()
                        .iter()
                        .map(|c| cache.get(c).unwrap())
                        .cloned()
                        .collect(),
                )
            });
            cache.insert(top.clone(), new_t);
        }
        computation.outputs = computation
            .outputs
            .iter()
            .map(|o| cache.get(o).unwrap().clone())
            .collect();
        if !self.cfg.waksman {
            for ram in &mut self.rams {
                if ram.is_covering_rom() {
                    ram.cfg.covering_rom = true;
                }
            }
        }
    }
}

/// Find arrays which are RAMs (i.e., accessed with a linear sequences of
/// selects, stores, and conditional stores) and
///   1. Replaces reads from these RAMs with new variables.
///   2. Builds a transcript for each RAM.
///
/// A conditional store must have form (ite C (store A I V) I) to be detected.
///
/// Limitations:
/// * This pass doesn't handle shared stuff very well. If there are two
///   different RAMs with the same init sequence of instructions, this pass will
///   not extract **either**.
pub fn extract(c: &mut Computation, cfg: AccessCfg) -> Vec<Ram> {
    let mut extractor = Extactor::new(c, cfg);
    extractor.traverse(c);
    extractor.rams
}

/// Extract any volatile RAMS from a computation, and emit checks.
pub fn apply(c: &mut Computation, cfg: &AccessCfg) {
    if c.ram_arrays.is_empty() {
        debug!("Skipping VolatileRam; no RAM arrays marked.");
        debug!("Found 0 RAMs");
        return;
    }
    let rams = extract(c, cfg.clone());
    debug!("Found {} transcripts", rams.len());
    if !rams.is_empty() {
        for ram in rams {
            super::checker::check_ram(c, ram);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::opt::cstore;

    #[test]
    fn non_ram() {
        env_logger::try_init().ok();
        let cs = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs ) (commitments))
                (precompute () () (#t ))
                (ram_arrays (#a (mod 11) #f0m11 4 ()))
                (set_default_modulus 11
                    (let
                        (
                            (c_array (#a (mod 11) #f0 4 ()))
                            (store_1 (store c_array #f0 #f1))
                            (store_2 (store c_array #f0 #f2))
                        )
                        (select (ite true store_1 store_2) #f0)
                    )
                )
            )
        ",
        );
        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let cfg = AccessCfg::default_from_field(field);
        let rams = extract(&mut cs2, cfg);
        extras::assert_all_vars_declared(&cs2);
        assert_eq!(0, rams.len());
        assert_eq!(cs, cs2);
    }

    #[test]
    fn simple_store_chain() {
        let cs = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs ) (commitments))
                    (precompute () () (#t ))
                    (ram_arrays (#a (mod 11) #f0m11 4 ()))
                    (set_default_modulus 11
                    (let
                        (
                            (c_array (#a (mod 11) #f0 4 ()))
                            (store_1 (store c_array #f0 #f1))
                            (store_2 (store store_1 #f1 #f2))
                        )
                        (select store_2 #f0)
                    ))
                )
            ",
        );
        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field.clone()));
        extras::assert_all_vars_declared(&cs2);
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(field, rams[0].cfg.field);
        assert_eq!(3, rams[0].accesses.len());
        assert_eq!(bool_lit(true), rams[0].accesses[0].write.b);
        assert_eq!(bool_lit(true), rams[0].accesses[1].write.b);
        assert_eq!(bool_lit(true), rams[0].accesses[0].active.b);
        assert_eq!(bool_lit(true), rams[0].accesses[1].active.b);
        assert_eq!(bool_lit(false), rams[0].accesses[2].write.b);
        assert_eq!(pf_lit(field.new_v(0)), rams[0].accesses[0].idx);
        assert_eq!(pf_lit(field.new_v(1)), rams[0].accesses[1].idx);
        assert_eq!(pf_lit(field.new_v(0)), rams[0].accesses[2].idx);
        assert_eq!(pf_lit(field.new_v(1)), rams[0].accesses[0].val);
        assert_eq!(pf_lit(field.new_v(2)), rams[0].accesses[1].val);
        assert!(rams[0].accesses[2].val.is_var());
    }

    #[test]
    fn c_store_chain() {
        env_logger::try_init().ok();
        let cs = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (a bool)) (commitments))
                    (precompute () () (#t ))
                    (ram_arrays (#a (mod 11) #f0m11 4 ()))
                    (set_default_modulus 11
                    (let
                        (
                            (c_array (#a (mod 11) #f0 4 ()))
                            (store_1 (ite a (store c_array #f0 #f1) c_array))
                            (store_2 (ite a (store store_1 #f1 #f1) store_1))
                        )
                        (select store_2 #f0)
                    ))
                )
            ",
        );
        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field.clone()));
        extras::assert_all_vars_declared(&cs2);
        let a = leaf_term(Op::Var("a".to_string(), Sort::Bool));
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(3, rams[0].accesses.len());
        assert_eq!(bool_lit(true), rams[0].accesses[0].write.b);
        assert_eq!(bool_lit(true), rams[0].accesses[1].write.b);
        assert_eq!(a, rams[0].accesses[0].active.b);
        assert_eq!(a, rams[0].accesses[1].active.b);
        assert_eq!(bool_lit(false), rams[0].accesses[2].write.b);
        assert_eq!(pf_lit(field.new_v(0)), rams[0].accesses[0].idx);
        assert_eq!(pf_lit(field.new_v(1)), rams[0].accesses[1].idx);
        assert_eq!(pf_lit(field.new_v(0)), rams[0].accesses[2].idx);
        assert_eq!(pf_lit(field.new_v(1)), rams[0].accesses[0].val);
        assert_eq!(pf_lit(field.new_v(1)), rams[0].accesses[1].val);
        assert!(rams[0].accesses[2].val.is_var());
    }

    #[test]
    fn mix_store_chain() {
        let a = leaf_term(Op::Var("a".to_string(), Sort::Bool));
        let cs = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (a bool)) (commitments))
                    (precompute () () (#t ))
                    (ram_arrays (#a (mod 11) #f0m11 4 ()))
                    (set_default_modulus 11
                    (let
                        (
                            (c_array (#a (mod 11) #f0 4 ()))
                            (store_1 (ite a (store c_array #f0 #f1) c_array))
                            (store_2 (store store_1 #f1 #f3))
                            (store_3 (ite a (store store_2 #f2 #f1) store_2))
                            (store_4 (store store_3 #f3 #f3))
                        )
                        (select store_4 #f0)
                    ))
                )
            ",
        );
        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field.clone()));
        extras::assert_all_vars_declared(&cs2);
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(5, rams[0].accesses.len());
        assert_eq!(a, rams[0].accesses[0].active.b);
        assert_eq!(bool_lit(true), rams[0].accesses[1].active.b);
        assert_eq!(a, rams[0].accesses[2].active.b);
        assert_eq!(bool_lit(true), rams[0].accesses[3].active.b);
        assert_eq!(bool_lit(false), rams[0].accesses[4].write.b);
        assert_eq!(pf_lit(field.new_v(0)), rams[0].accesses[0].idx);
        assert_eq!(pf_lit(field.new_v(1)), rams[0].accesses[1].idx);
        assert_eq!(pf_lit(field.new_v(2)), rams[0].accesses[2].idx);
        assert_eq!(pf_lit(field.new_v(3)), rams[0].accesses[3].idx);
        assert_eq!(pf_lit(field.new_v(0)), rams[0].accesses[4].idx);
    }

    #[test]
    fn two_rams_and_one_non_ram() {
        let cs = text::parse_computation(
            b"
               (computation
                   (metadata (parties ) (inputs (a bool)) (commitments))
                   (precompute () () (#t ))
                   (ram_arrays (#a (mod 11) #f000m11 4 ()))
                   (set_default_modulus 11
                   (let
                       (
                           ; connected component 0: simple store chain
                           (c_array (#a (mod 11) #f000 4 ()))
                           (store_0_1 (store c_array #f0 #f001))
                           (store_0_2 (store store_0_1 #f1 #f001))
                           (select_0 (select store_0_2 #f0))

                           ; connected component 1: conditional store chain
                           (store_1_1 (ite a (store c_array #f0 #f010) c_array))
                           (store_1_2 (ite a (store store_1_1 #f1 #f010) store_1_1))
                           (select_1 (select store_1_2 #f0))

                           ; connected component 2: not a RAM
                           (store_2_1 (ite a (store c_array #f0 #f011) c_array))
                           (store_2_2 (ite a (store c_array #f0 #f011) c_array))
                           (ite_ (ite true store_2_1 store_2_2))
                           (select_2 (select ite_ #f0))
                       )
                       (+ select_0 select_1 select_2)
                   ))
               )
           ",
        );

        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field));
        extras::assert_all_vars_declared(&cs2);
        assert_eq!(1, cs2.outputs.len());
        assert_ne!(cs, cs2);
        assert_eq!(2, rams.len());
        assert_eq!(3, rams[0].accesses.len());
        assert_eq!(3, rams[1].accesses.len());
    }

    #[test]
    fn nested() {
        env_logger::try_init().ok();
        let cs = text::parse_computation(
            b"
               (computation
                   (metadata (parties ) (inputs (a bool)) (commitments))
                   (precompute () () (#t ))
                   (ram_arrays (#a (mod 11) #f0m11 16 ()))
                   (set_default_modulus 11
                   (let
                        (
                           ; connected component 0: simple store chain
                           (c_array (#a (mod 11) (#a (mod 11) #f0 16 ()) 4 ()))
                           (c_in_array (#a (mod 11) #f0 16 ()))
                           (store_1 (store c_array #f0 c_in_array))
                        )
                        (select (select store_1 #f0) #f0)
                    ))
               )
           ",
        );

        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field));
        assert_eq!(0, rams.len());
        assert_eq!(cs, cs2);
    }

    #[test]
    fn rom() {
        let cs = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs ) (commitments))
                    (precompute () () (#t ))
                    (ram_arrays (#a (mod 11) #f0m11 4 ()))
                    (set_default_modulus 11
                    (let
                        (
                            (c_array (#a (mod 11) #f0 4 ()))
                            (x0 (select c_array #f0))
                            (x1 (select c_array #f1))
                            (x2 (select c_array #f2))
                            (x3 (select c_array #f3))
                        )
                        (+ x0 x1 x2 x3)
                    ))
                )
            ",
        );
        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field.clone()));
        extras::assert_all_vars_declared(&cs2);
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(4, rams[0].accesses.len());
    }

    #[test]
    fn multi_arm_tree() {
        let cs = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs ) (commitments))
                    (precompute () () (#t ))
                    (ram_arrays (#a (mod 11) #f0m11 4 ()))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#a (mod 11) #f0 4 ()))
                            (a1 (store a0 #f0 #f1))
                            (x0 (select a1 #f0))
                            (x1 (select a1 #f1))
                            (a2 (store a1 #f0 #f1))
                            (x2 (select a2 #f2))
                            (x3 (select a2 #f3))
                            (a3 (store a2 #f1 #f1))
                            (x4 (select a3 #f0))
                            (x5 (select a3 #f1))
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        let mut cs2 = cs.clone();
        cstore::parse(&mut cs2);
        let field = FieldT::from(rug::Integer::from(11));
        let rams = extract(&mut cs2, AccessCfg::default_from_field(field.clone()));
        extras::assert_all_vars_declared(&cs2);
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(9, rams[0].accesses.len());
        println!("{:?}", rams[0].accesses);
        assert_eq!(bool_lit(true), rams[0].accesses[0].write.b);
        assert_eq!(bool_lit(false), rams[0].accesses[1].write.b);
        assert_eq!(bool_lit(false), rams[0].accesses[2].write.b);
        assert_eq!(bool_lit(true), rams[0].accesses[3].write.b);
        assert_eq!(bool_lit(false), rams[0].accesses[4].write.b);
        assert_eq!(bool_lit(false), rams[0].accesses[5].write.b);
        assert_eq!(bool_lit(true), rams[0].accesses[6].write.b);
        assert_eq!(bool_lit(false), rams[0].accesses[7].write.b);
        assert_eq!(bool_lit(false), rams[0].accesses[8].write.b);
    }

    #[cfg(feature = "poly")]
    #[test]
    fn length_4() {
        env_logger::try_init().ok();
        let mut cs = text::parse_computation(
            b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (return (mod 101))
                    )
                    ; (commitments (commitment A))
                    (commitments)
                )
                (precompute () () (#t ))
                (ram_arrays ((fill (mod 101) 4) #f0m11))
                (set_default_modulus 101
                (let(
                  ('1 ((fill (mod 101) 4) #f0))
                  ('2 (cstore '1 #f0 #f4 false))
                  ('3 (cstore '2 #f1 #f4 true))
                  ('4 (cstore '3 #f3 #f4 false))
                )
                (= return (select '4 #f1))
                ))
            )
        ",
        );
        let values = text::parse_value_map(
            b"
            (set_default_modulus 101
            (let (
                (return #f4)
            ) false ; ignored
            ))
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
        let field = FieldT::from(rug::Integer::from(101));
        let cfg = AccessCfg::default_from_field(field);
        apply(&mut cs, &cfg);
        println!("{}", text::serialize_computation(&cs));
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
    }
}
