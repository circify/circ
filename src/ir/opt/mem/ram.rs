/// RAM extraction
///
/// See the documentation for [extract]
use log::trace;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

#[derive(Debug)]
/// An access to a RAM
pub struct Access {
    /// Whether this is a read or a write.
    pub is_write: Term,
    /// The index/address.
    pub idx: Term,
    /// The value written or read.
    pub val: Term,
}

impl Access {
    fn new_read(idx: Term, val: Term) -> Self {
        Self {
            idx,
            val,
            is_write: bool_lit(false),
        }
    }
    fn new_write(idx: Term, val: Term, guard: Term) -> Self {
        Self {
            idx,
            val,
            is_write: guard,
        }
    }
}

#[derive(Debug)]
/// A RAM transcript
pub struct Ram {
    /// The unique id of this RAM
    pub id: usize,
    /// The starting value of all cells
    pub init_val: Value,
    /// The size
    pub size: usize,
    /// The list of accesses (in access order)
    pub accesses: Vec<Access>,
    /// The index sort
    pub idx_sort: Sort,
    /// The value sort
    pub val_sort: Sort,
}

impl Ram {
    fn new(id: usize, const_: Array) -> Self {
        assert_eq!(const_.map.len(), 0);
        Ram {
            id,
            val_sort: const_.default.sort(),
            idx_sort: const_.key_sort,
            accesses: vec![],
            size: const_.size,
            init_val: *const_.default,
        }
    }
    fn new_read(&mut self, idx: Term, computation: &mut Computation, read_value: Term) -> Term {
        let val_name = format!("__ram_{}_{}", self.id, self.accesses.len());
        debug_assert_eq!(&check(&idx), &self.idx_sort);
        let var = computation.new_var(
            &val_name,
            check(&read_value),
            Some(crate::ir::proof::PROVER_ID),
            Some(read_value),
        );
        self.accesses.push(Access::new_read(idx, var.clone()));
        var
    }
    fn new_write(&mut self, idx: Term, val: Term, guard: Term) {
        debug_assert_eq!(&check(&idx), &self.idx_sort);
        debug_assert_eq!(&check(&val), &self.val_sort);
        debug_assert_eq!(&check(&guard), &Sort::Bool);
        self.accesses.push(Access::new_write(idx, val, guard));
    }
}

/// Parse `ite` as a conditional store (arr, idx, val, guard)
fn parse_cond_store(ite: &Term) -> Option<ConditionalStore> {
    if ite.op() == &Op::Ite && ite.cs()[1].op() == &Op::Store && ite.cs()[1].cs()[0] == ite.cs()[2]
    {
        Some(ConditionalStore {
            arr: ite.cs()[2].clone(),
            idx: ite.cs()[1].cs()[1].clone(),
            val: ite.cs()[1].cs()[2].clone(),
            guard: ite.cs()[0].clone(),
            store: ite.cs()[1].clone(),
        })
    } else {
        None
    }
}

#[derive(Debug)]
/// Data about a conditional store: term = (ite guard (store arr idx val) arr)
///
/// The store field is (store arr idx val)
struct ConditionalStore {
    arr: Term,
    idx: Term,
    val: Term,
    guard: Term,
    store: Term,
}

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
    /// Set of all array terms.
    array_terms: TermSet,
    /// Set of non-RAM array terms.
    non_ram: TermSet,
}

impl ArrayGraph {
    fn new(c: &Computation) -> Self {
        let term_parents = extras::parents_map(c);
        let mut c_stores = TermMap::default();
        let mut ps = TermMap::default();
        let mut cs = TermMap::default();
        let mut arrs = TermSet::default();
        let mut subsumed = TermSet::default();
        // We go parent->children to see conditional stores before their subsumed stores.
        // clippy thinks this is needless, but we need it for the reverse iteration.
        #[allow(clippy::needless_collect)]
        let terms: Vec<_> = c.terms_postorder().collect();
        for t in terms.into_iter().rev() {
            let mut is_c_store = false;
            if let Some(c_store) = parse_cond_store(&t) {
                if term_parents.get(&c_store.store).unwrap().len() == 1 {
                    trace!("cond store: {}", t);
                    subsumed.insert(c_store.store.clone());
                    ps.entry(c_store.arr.clone())
                        .or_insert_with(Vec::new)
                        .push(t.clone());
                    cs.entry(t.clone())
                        .or_insert_with(Vec::new)
                        .push(c_store.arr.clone());
                    arrs.insert(t.clone());
                    c_stores.insert(t.clone(), c_store);
                    is_c_store = true;
                }
            }
            if !is_c_store && !subsumed.contains(&t) {
                if let Sort::Array(..) = check(&t) {
                    for c in t.cs() {
                        if let Sort::Array(..) = check(c) {
                            arrs.insert(t.clone());
                            ps.entry(c.clone()).or_insert_with(Vec::new).push(t.clone());
                            cs.entry(t.clone()).or_insert_with(Vec::new).push(c.clone());
                        }
                    }
                }
            }
        }
        let mut non_ram: TermSet = TermSet::default();
        {
            let mut stack: Vec<Term> = arrs
                .iter()
                .filter(|a| {
                    !a.is_const()
                        && (ps.get(a).map(|ps| ps.len() > 1).unwrap_or(false)
                            || cs.get(a).map(|cs| cs.len() > 1).unwrap_or(false))
                })
                .cloned()
                .collect();
            while let Some(t) = stack.pop() {
                if !t.is_const() && !non_ram.contains(&t) {
                    trace!("Non-RAM: {}", t);
                    non_ram.insert(t.clone());
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
            array_terms: arrs,
            non_ram,
        }
    }
    fn is_ram(&self, t: &Term) -> bool {
        !t.is_const() && self.array_terms.contains(t) && !self.non_ram.contains(t)
    }
}

#[derive(Debug)]
struct Extactor {
    rams: Vec<Ram>,
    term_ram: TermMap<RamId>,
    read_terms: TermMap<Term>,
    graph: ArrayGraph,
}

type RamId = usize;

impl Extactor {
    fn new(c: &Computation) -> Self {
        let graph = ArrayGraph::new(c);
        Self {
            rams: Vec::new(),
            term_ram: TermMap::default(),
            read_terms: TermMap::default(),
            graph,
        }
    }
    // If this term is a constant array, start a new RAM. Otherwise, look this term up.
    fn get_or_start(&mut self, t: &Term) -> RamId {
        match &t.op() {
            Op::Const(Value::Array(a)) => {
                let id = self.rams.len();
                self.rams.push(Ram::new(id, a.clone()));
                id
            }
            _ => *self
                .term_ram
                .get(t)
                .unwrap_or_else(|| panic!("No RAM for term {}", t)),
        }
    }
}

impl RewritePass for Extactor {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        t: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        // First, we rewrite RAM terms.
        if self.graph.is_ram(t) {
            // Since this is a "RAM" term, it is non-constant and either a c-store or a store.
            assert!(matches!(t.op(), Op::Store | Op::Ite));
            debug_assert!(self.graph.children.get(t).is_some());
            debug_assert_eq!(1, self.graph.children.get(t).unwrap().len());
            // Get dependency's RAM
            let child = self.graph.children.get(t).unwrap()[0].clone();
            let ram_id = self.get_or_start(&child);
            let ram = &mut self.rams[ram_id];
            // Build new term, and parse as a c-store
            let new = term(t.op().clone(), rewritten_children());
            let c_store = parse_cond_store(&new).unwrap_or_else(|| {
                // this is a plain store then, map it to a c-store
                assert_eq!(&Op::Store, new.op());
                ConditionalStore {
                    arr: new.cs()[0].clone(),
                    idx: new.cs()[1].clone(),
                    val: new.cs()[2].clone(),
                    guard: bool_lit(true),
                    store: bool_lit(false), // dummy; unused.
                }
            });
            // Add the write to the RAM
            ram.new_write(c_store.idx, c_store.val, c_store.guard);
            let id = ram.id;
            self.term_ram.insert(t.clone(), id);
            None
        } else {
            match &t.op() {
                // Rewrite select's whose array is a RAM term
                Op::Select if self.graph.is_ram(&t.cs()[0]) => {
                    let ram_id = self.get_or_start(&t.cs()[0]);
                    let ram = &mut self.rams[ram_id];
                    let read_value = ram.new_read(t.cs()[1].clone(), computation, t.clone());
                    self.read_terms.insert(t.clone(), read_value.clone());
                    Some(read_value)
                }
                _ => None,
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
#[allow(dead_code)]
pub fn extract(c: &mut Computation) -> Vec<Ram> {
    let mut extractor = Extactor::new(c);
    extractor.traverse(c);
    extractor.rams
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn non_ram() {
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () () ())
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (bv 4) #x0 4 ()))
                        (store_1 (store c_array #x0 #x1))
                        (store_2 (store c_array #x0 #x2))
                    )
                    (select (ite true store_1 store_2) #x0)
                )
            )
        ",
        );
        let mut cs2 = cs.clone();
        let rams = extract(&mut cs2);
        extras::assert_all_vars_declared(&cs2);
        assert_eq!(0, rams.len());
        assert_eq!(cs, cs2);
    }

    #[test]
    fn simple_store_chain() {
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () () ())
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (bv 4) #b000 4 ()))
                        (store_1 (store c_array #x0 #b001))
                        (store_2 (store store_1 #x1 #b010))
                    )
                    (select store_2 #x0)
                )
            )
        ",
        );
        let mut cs2 = cs.clone();
        let rams = extract(&mut cs2);
        extras::assert_all_vars_declared(&cs2);
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(Sort::BitVector(4), rams[0].idx_sort);
        assert_eq!(Sort::BitVector(3), rams[0].val_sort);
        assert_eq!(3, rams[0].accesses.len());
        assert_eq!(bool_lit(true), rams[0].accesses[0].is_write);
        assert_eq!(bool_lit(true), rams[0].accesses[1].is_write);
        assert_eq!(bool_lit(false), rams[0].accesses[2].is_write);
        assert_eq!(bv_lit(0, 4), rams[0].accesses[0].idx);
        assert_eq!(bv_lit(1, 4), rams[0].accesses[1].idx);
        assert_eq!(bv_lit(0, 4), rams[0].accesses[2].idx);
        assert_eq!(bv_lit(1, 3), rams[0].accesses[0].val);
        assert_eq!(bv_lit(2, 3), rams[0].accesses[1].val);
        assert!(rams[0].accesses[2].val.is_var());
        dbg!(cs2);
    }

    #[test]
    fn c_store_chain() {
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () ((a bool)) ())
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (bv 4) #b000 4 ()))
                        (store_1 (ite a (store c_array #x0 #b001) c_array))
                        (store_2 (ite a (store store_1 #x1 #b001) store_1))
                    )
                    (select store_2 #x0)
                )
            )
        ",
        );
        let mut cs2 = cs.clone();
        let rams = extract(&mut cs2);
        extras::assert_all_vars_declared(&cs2);
        let a = leaf_term(Op::Var("a".to_string(), Sort::Bool));
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(Sort::BitVector(4), rams[0].idx_sort);
        assert_eq!(Sort::BitVector(3), rams[0].val_sort);
        assert_eq!(3, rams[0].accesses.len());
        assert_eq!(a, rams[0].accesses[0].is_write);
        assert_eq!(a, rams[0].accesses[1].is_write);
        assert_eq!(bool_lit(false), rams[0].accesses[2].is_write);
        assert_eq!(bv_lit(0, 4), rams[0].accesses[0].idx);
        assert_eq!(bv_lit(1, 4), rams[0].accesses[1].idx);
        assert_eq!(bv_lit(0, 4), rams[0].accesses[2].idx);
        assert_eq!(bv_lit(1, 3), rams[0].accesses[0].val);
        assert_eq!(bv_lit(1, 3), rams[0].accesses[1].val);
        assert!(rams[0].accesses[2].val.is_var());
    }

    #[test]
    fn mix_store_chain() {
        let a = leaf_term(Op::Var("a".to_string(), Sort::Bool));
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () ((a bool)) ())
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (bv 4) #b000 4 ()))
                        (store_1 (ite a (store c_array #x0 #b001) c_array))
                        (store_2 (store store_1 #x1 #b011))
                        (store_3 (ite a (store store_2 #x2 #b001) store_2))
                        (store_4 (store store_3 #x3 #b011))
                    )
                    (select store_4 #x0)
                )
            )
        ",
        );
        let mut cs2 = cs.clone();
        let rams = extract(&mut cs2);
        extras::assert_all_vars_declared(&cs2);
        assert_ne!(cs, cs2);
        assert_eq!(1, rams.len());
        assert_eq!(Sort::BitVector(4), rams[0].idx_sort);
        assert_eq!(Sort::BitVector(3), rams[0].val_sort);
        assert_eq!(5, rams[0].accesses.len());
        assert_eq!(a, rams[0].accesses[0].is_write);
        assert_eq!(bool_lit(true), rams[0].accesses[1].is_write);
        assert_eq!(a, rams[0].accesses[2].is_write);
        assert_eq!(bool_lit(true), rams[0].accesses[3].is_write);
        assert_eq!(bool_lit(false), rams[0].accesses[4].is_write);
        assert_eq!(bv_lit(0, 4), rams[0].accesses[0].idx);
        assert_eq!(bv_lit(1, 4), rams[0].accesses[1].idx);
        assert_eq!(bv_lit(2, 4), rams[0].accesses[2].idx);
        assert_eq!(bv_lit(3, 4), rams[0].accesses[3].idx);
        assert_eq!(bv_lit(0, 4), rams[0].accesses[4].idx);
    }

    #[test]
    fn two_rams_and_one_non_ram() {
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () ((a bool)) ())
                (precompute () () (#t ))
                (let
                    (
                        ; connected component 0: simple store chain
                        (c_array (#a (bv 4) #b000 4 ()))
                        (store_0_1 (store c_array #x0 #b001))
                        (store_0_2 (store store_0_1 #x1 #b001))
                        (select_0 (select store_0_2 #x0))

                        ; connected component 1: conditional store chain
                        (store_1_1 (ite a (store c_array #x0 #b010) c_array))
                        (store_1_2 (ite a (store store_1_1 #x1 #b010) store_1_1))
                        (select_1 (select store_1_2 #x0))

                        ; connected component 2: not a RAM
                        (store_2_1 (ite a (store c_array #x0 #b011) c_array))
                        (store_2_2 (ite a (store c_array #x0 #b011) c_array))
                        (ite_ (ite true store_2_1 store_2_2))
                        (select_2 (select ite_ #x0))
                    )
                    (bvand select_0 select_1 select_2)
                )
            )
        ",
        );

        let mut cs2 = cs.clone();
        let rams = extract(&mut cs2);
        extras::assert_all_vars_declared(&cs2);
        assert_eq!(1, cs2.outputs.len());
        assert_ne!(cs, cs2);
        assert_eq!(2, rams.len());
        assert_eq!(cs.outputs[0].cs()[2], cs2.outputs[0].cs()[2]);
        assert_eq!(3, rams[0].accesses.len());
        assert_eq!(3, rams[1].accesses.len());
    }

    #[test]
    fn nested() {
        let c_array = leaf_term(Op::Const(Value::Array(Array::default(
            Sort::BitVector(4),
            &Sort::Array(
                Box::new(Sort::BitVector(4)),
                Box::new(Sort::BitVector(4)),
                16,
            ),
            4,
        ))));
        let c_in_array = leaf_term(Op::Const(Value::Array(Array::default(
            Sort::BitVector(4),
            &Sort::BitVector(4),
            16,
        ))));
        let store_1 = term![Op::Store; c_array, bv_lit(0, 4), c_in_array];
        let select = term![Op::Select; term![Op::Select; store_1, bv_lit(0, 4)], bv_lit(0, 4)];
        let mut cs = Computation::default();
        cs.outputs.push(select);
        let mut cs2 = cs.clone();
        let rams = extract(&mut cs2);
        assert_eq!(0, rams.len());
        assert_eq!(cs, cs2);
    }
}
