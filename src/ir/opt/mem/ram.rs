// TODO: remove
#![warn(warnings)]

use log::debug;

use crate::ir::opt::visit::ProgressAnalysisPass;
use crate::ir::term::extras::Letified;
use crate::ir::term::*;

/// Computes which terms are not RAM
#[derive(Debug)]
struct NonRamComputer {
    non_ram: TermSet,
}

impl NonRamComputer {
    /// Mark `t` as non-RAM. Return whether this fact is new.
    fn mark(&mut self, t: &Term) -> bool {
        if t.is_const() {
            self.non_ram.insert(t.clone())
        } else {
            false
        }
    }

    fn bi_implicate(&mut self, a: &Term, b: &Term) -> bool {
        if !a.is_const() && !b.is_const() {
            match (self.non_ram.contains(a), self.non_ram.contains(b)) {
                (false, true) => self.non_ram.insert(a.clone()),
                (true, false) => self.non_ram.insert(b.clone()),
                _ => false,
            }
        } else {
            false
        }
    }

    fn new(mut parents: &TermMap<Vec<Term>>) -> Self {
        let mut this = NonRamComputer {
            non_ram: TermSet::new(),
        };
        for (c, ps) in parents {
            if ps.iter().filter(|p| p.op == Op::Store).count() > 1 {
                this.mark(c);
            }
        }
        this
    }
}

impl ProgressAnalysisPass for NonRamComputer {
    fn visit(&mut self, term: &Term) -> bool {
        let mut progress = false;
        if let s @ Sort::Array(..) = check(term) {
            match &term.op {
                Op::Ite => {
                    if term.cs[1].op != Op::Store || term.cs[1].cs[0] != term.cs[2] {
                        debug!("Non-RAM {}", extras::Letified(term.clone()));
                        progress = self.mark(&term) || progress;
                        progress = self.mark(&term.cs[1]) || progress;
                        progress = self.mark(&term.cs[2]) || progress;
                    }
                }
                Op::Store => {
                    progress = self.bi_implicate(term, &term.cs[0]) || progress;
                }
                Op::Var(..) => panic!("array var in ram extraction"),
                _ => {}
            }
        } else {
            match &term.op {
                Op::Select => {
                    progress = self.bi_implicate(term, &term.cs[0]) || progress;
                }
                _ => {}
            }
        }
        progress
    }
}

#[derive(Debug)]
struct Access {
    is_write: Term,
    idx: Term,
    val: Term,
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
struct Ram {
    id: usize,
    init_val: Value,
    size: usize,
    accesses: Vec<Access>,
    idx_sort: Sort,
    val_sort: Sort,
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
    fn new_read(&mut self, idx: Term) -> Term {
        let val_name = format!("__ram_{}_{}", self.id, self.accesses.len());
        debug_assert_eq!(&check(&idx), &self.idx_sort);
        let var = leaf_term(Op::Var(val_name, self.val_sort.clone()));
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
    if ite.op == Op::Ite && ite.cs[1].op == Op::Store && ite.cs[1].cs[0] == ite.cs[2] {
        Some(ConditionalStore {
            arr: ite.cs[2].clone(),
            idx: ite.cs[1].cs[1].clone(),
            val: ite.cs[1].cs[2].clone(),
            guard: ite.cs[0].clone(),
            store: ite.cs[1].clone(),
        })
    } else {
        None
    }
}

struct ConditionalStore {
    arr: Term,
    idx: Term,
    val: Term,
    guard: Term,
    store: Term,
}

struct ConditionalStoreData {
    parents: TermMap<Vec<Term>>,
    c_stores: TermMap<ConditionalStore>,
    subsumed_stores: TermSet,
    stores: TermSet,
    nca_parents: TermMap<Vec<Term>>,
    nca_children: TermMap<Vec<Term>>,
}

impl ConditionalStoreData {
    fn new(c: &Computation) -> Self {
        let parents = extras::parents_map(c);
        let mut c_stores = TermMap::default();
        let mut subsumed_stores = TermSet::default();
        for t in c.terms_postorder() {
            if let Some(c_store) = parse_cond_store(t) {
                if parents.get(&c_store.store).unwrap().len() == 1 {
                    debug!("cond store: {}", Letified(t.clone()));
                    subsumed_stores.insert(c_store.store.clone());
                    c_stores.insert(t, c_store);
                }
            }
        }
        let stores: TermSet = c
            .terms_postorder()
            .filter(|t| !t.is_const() && matches!(check(t), Sort::Array(..)))
            .collect();
        let mut nca_parents: TermMap<Vec<Term>> = stores.iter().cloned().map(|s| (s, Vec::new())).collect();
        let mut nca_children: TermMap<Vec<Term>> = stores.iter().cloned().map(|s| (s, Vec::new())).collect();
        for s in &stores {
            if let Some(c_store) = c_stores.get(s) {
                nca_parents.get_mut(&c_store.arr).unwrap().push(s.clone());
                nca_parents.get_mut(s).unwrap().push(c_store.arr.clone());
            } else {
                match &s.op {
                    Op::Ite => {
                        nca_parents.get_mut(&c_store.arr).unwrap().push(s.clone());
                        nca_parents.get_mut(s).unwrap().push(c_store.arr.clone());

                    }
                }
            }
        }
        Self {
            parents,
            c_stores,
            subsumed_stores,
        }
    }
}

#[derive(Debug)]
struct Extactor {
    rams: Vec<Ram>,
    term_ram: TermMap<RamId>,
    read_terms: TermMap<Term>,
}

type RamId = usize;

impl Extactor {
    // If this term is a constant array, start a new RAM. Otherwise, look this term up.
    fn get_or_start(&mut self, t: &Term) -> RamId {
        match &t.op {
            Op::Const(Value::Array(a)) => {
                let id = self.rams.len();
                self.rams.push(Ram::new(id, a.clone()));
                id
            }
            _ => *self
                .term_ram
                .get(t)
                .unwrap_or_else(|| panic!("No RAM for term {}", extras::Letified(t))),
        }
    }
    fn visit(&mut self, t: &Term) {
        match &t.op {
            Op::Select => {
                let ram_id = self.get_or_start(&t.cs[0]);
                let ram = &mut self.rams[ram_id];
                let read_value = ram.new_read(t.cs[1].clone());
                self.read_terms.insert(t.clone(), read_value.clone());
            }
            Op::Store => {
                let ram_id = self.get_or_start(&t.cs[0]);
                let ram = &mut self.rams[ram_id];
                let read_value = ram.new_read(t.cs[1].clone());
                self.read_terms.insert(t.clone(), read_value.clone());
            }
        }
    }
}

#[cfg(test)]
mod test {}
