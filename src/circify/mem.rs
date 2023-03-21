//! The stack-allocation memory manager

use crate::ir::term::*;
use std::collections::HashMap;

/// Identifier for an Allocation block in memory
pub type AllocId = usize;

struct Alloc {
    addr_width: usize,
    val_width: usize,
    size: usize,
    cur_term: Term,
}

impl Alloc {
    fn new(addr_width: usize, val_width: usize, size: usize, cur_term: Term) -> Self {
        Self {
            addr_width,
            val_width,
            size,
            cur_term,
        }
    }

    fn var(&self) -> &Term {
        &self.cur_term
    }
}

/// Manages a circuit-embedded stack.
pub struct MemManager {
    allocs: HashMap<AllocId, Alloc>,
    next_id: usize,
}

impl Default for MemManager {
    /// Create a new manager, with an empty stack.
    fn default() -> Self {
        Self {
            allocs: HashMap::default(),
            next_id: 0,
        }
    }
}

impl MemManager {
    /// Returns the next allocation identifier, and advances it.
    fn take_next_id(&mut self) -> usize {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    /// Allocate a new stack array, equal to `array`.
    pub fn allocate(&mut self, array: Term) -> AllocId {
        let s = check(&array);
        if let Sort::Array(box_addr_width, box_val_width, size) = s {
            if let Sort::BitVector(addr_width) = *box_addr_width {
                if let Sort::BitVector(val_width) = *box_val_width {
                    let id = self.take_next_id();
                    let alloc = Alloc::new(addr_width, val_width, size, array);
                    self.allocs.insert(id, alloc);
                    id
                } else {
                    panic!("Cannot access val_width")
                }
            } else {
                panic!("Cannot access addr_width")
            }
        } else {
            panic!("Cannot allocate array of sort: {}", s)
        }
    }

    /// Allocate a new zero-initialized stack array.
    ///
    /// ## Parameters
    ///
    /// * `size`: number of elements
    /// * `addr_width`: number of bits in an index
    /// * `val_width`: number of bits in a value
    ///
    /// ## Returns
    ///
    /// Returns a (concrete) allocation identifier which can be used to access this allocation.
    pub fn zero_allocate(&mut self, size: usize, addr_width: usize, val_width: usize) -> AllocId {
        self.allocate(term![Op::Const(Value::Array(Array::default(
            Sort::BitVector(addr_width),
            &Sort::BitVector(val_width),
            size
        )))])
    }

    /// Load the value of index `offset` from the allocation `id`.
    pub fn load(&self, id: AllocId, offset: Term) -> Term {
        let alloc = self.allocs.get(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        term![Op::Select; alloc.var().clone(), offset]
    }

    /// Write the value `val` to index `offset` in the allocation `id`.
    pub fn store(&mut self, id: AllocId, offset: Term, val: Term, cond: Term) {
        let alloc = self.allocs.get_mut(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        assert_eq!(alloc.val_width, check(&val).as_bv());
        let old = alloc.cur_term.clone();
        let new = term![Op::Store; alloc.var().clone(), offset, val];
        let ite_store = term![Op::Ite; cond, new, old];
        alloc.cur_term = ite_store;
    }

    /// Replace the stored term in the allocation `id` with the value `val`.
    pub fn replace(&mut self, id: AllocId, val: Term) {
        let alloc = self.allocs.get_mut(&id).expect("Missing allocation");
        alloc.cur_term = val;
    }

    /// Is `offset` in bounds for the allocation `id`?
    pub fn in_bounds(&self, id: AllocId, offset: Term) -> Term {
        let alloc = self.allocs.get(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        term![Op::BvBinPred(BvBinPred::Ult); offset, bv_lit(alloc.size, alloc.addr_width)]
    }

    /// Get size of the array at the allocation `id`
    pub fn get_size(&self, id: AllocId) -> usize {
        let alloc = self.allocs.get(&id).expect("Missing allocation");
        alloc.size
    }
}

#[cfg(all(feature = "smt", feature = "test", feature = "zok"))]
mod test {
    use super::*;
    use crate::target::smt::check_sat;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn bv_var(s: &str, w: usize) -> Term {
        leaf_term(Op::Var(s.to_owned(), Sort::BitVector(w)))
    }

    fn sat_test() {
        let cs = Rc::new(RefCell::new(Computation::new(false)));
        let mut mem = MemManager::default();
        let id0 = mem.zero_allocate(6, 4, 8);
        let _id1 = mem.zero_allocate(6, 4, 8);
        mem.store(
            id0,
            bv_lit(3, 4),
            bv_lit(2, 8),
            leaf_term(Op::Const(Value::Bool(true))),
        );
        let a = mem.load(id0, bv_lit(3, 4));
        let b = mem.load(id0, bv_lit(1, 4));
        let t = term![Op::BvBinPred(BvBinPred::Ugt); a, b];
        cs.borrow_mut().assert(t);
        let sys = term(
            Op::BoolNaryOp(BoolNaryOp::And),
            cs.borrow().outputs().clone(),
        );
        assert!(check_sat(&sys))
    }

    fn unsat_test() {
        let cs = Rc::new(RefCell::new(Computation::new(false)));
        let mut mem = MemManager::default();
        let id0 = mem.zero_allocate(6, 4, 8);
        let _id1 = mem.zero_allocate(6, 4, 8);
        mem.store(
            id0,
            bv_lit(3, 4),
            bv_var("a", 8),
            leaf_term(Op::Const(Value::Bool(true))),
        );
        let a = mem.load(id0, bv_lit(3, 4));
        let b = mem.load(id0, bv_lit(3, 4));
        let t = term![Op::Not; term![Op::Eq; a, b]];
        cs.borrow_mut().assert(t);
        let sys = term(
            Op::BoolNaryOp(BoolNaryOp::And),
            cs.borrow().outputs().clone(),
        );
        assert!(!check_sat(&sys))
    }
}
