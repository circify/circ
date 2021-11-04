//! The stack-allocation memory manager

use crate::ir::term::*;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Identifier for an Allocation block in memory
pub type AllocId = usize;

struct Alloc {
    _id: AllocId,
    addr_width: usize,
    val_width: usize,
    _cur_ver: usize,
    size: usize,
    cur_term: Term, 
}

impl Alloc {
    /// Get the variable for the next version, and advance the next version.
    // fn next_var(&mut self) {
    //     self.cur_ver += 1;
    //     let t = leaf_term(Op::Var(
    //         format!("mem_{}_v{}", self.id, self.cur_ver),
    //         self.sort(),
    //     ));
    //     self.cur_term = t;
    // }

    // fn sort(&self) -> Sort {
    //     Sort::Array(
    //         Box::new(Sort::BitVector(self.addr_width)),
    //         Box::new(Sort::BitVector(self.val_width)),
    //         self.size,
    //     )
    // }

    fn new(id: AllocId, addr_width: usize, val_width: usize, size: usize, cur_term: Term) -> Self {
        Self {
            _id: id,
            addr_width,
            val_width,
            size,
            _cur_ver: 0,
            cur_term: cur_term,
        }
    }

    fn var(&self) -> &Term {
        &self.cur_term
    }
}

/// Manages a circuit-embedded stack.
pub struct MemManager {
    // TODO make this public or accessible?
    allocs: HashMap<AllocId, Alloc>,
    next_id: usize,
    _cs: Rc<RefCell<Computation>>,
}

impl MemManager {
    /// Create a new manager, with an empty stack.
    pub fn new(cs: Rc<RefCell<Computation>>) -> Self {
        Self {
            allocs: HashMap::new(),
            next_id: 0,
            _cs: cs,
        }
    }

    /// Returns the next allocation identifier, and advances it.
    fn take_next_id(&mut self) -> usize {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    // fn assert(&mut self, t: Term) {
    //     debug_assert!(check(&t) == Sort::Bool);
    //     self.cs.borrow_mut().assert(t);
    // }

    /// Allocate a new stack array, equal to `array`.
    pub fn allocate(&mut self, array: Term) -> AllocId {
        let s = check(&array);
        if let Sort::Array(box Sort::BitVector(addr_width), box Sort::BitVector(val_width), size) =
            s
        {
            let id = self.take_next_id();
            let alloc = Alloc::new(id, addr_width, val_width, size, array);

            // let v = alloc.var().clone();
            // TODO: add computations to ctx without assert
            // if let Op::Var(n, _) = &v.op {
            //     self.cs.borrow_mut().eval_and_save(&n, &array);
            // } else {
            //     unreachable!()
            // }
            // self.assert(term![Op::Eq; v, array]);
            // self.cs.borrow_mut().outputs.push(term![Op::Eq; v, array]);

            // output some term 
            // store term with name somewhere in context? 

            self.allocs.insert(id, alloc);
            id
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
        self.allocate(term![Op::ConstArray(Sort::BitVector(addr_width), size); leaf_term(Op::Const(Value::BitVector(BitVector::zeros(val_width))))])
    }

    /// Load the value of index `offset` from the allocation `id`.
    pub fn load(&self, id: AllocId, offset: Term) -> Term {
        let alloc = self.allocs.get(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        term![Op::Select; alloc.var().clone(), offset]
    }

    /// Write the value `val` to index `offset` in the allocation `id`.
    pub fn store(&mut self, id: AllocId, offset: Term, val: Term) {
        let alloc = self.allocs.get_mut(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        assert_eq!(alloc.val_width, check(&val).as_bv());
        let new = term![Op::Store; alloc.var().clone(), offset, val];
        alloc.cur_term = new;
        // alloc.next_var();
        // let v = alloc.var().clone();

        // TODO: add computations to ctx without assert
        // if let Op::Var(n, _) = &v.op {
        //     self.cs.borrow_mut().eval_and_save(&n, &new);
        // } else {
        //     unreachable!()
        // }
        // self.assert(term![Op::Eq; v, new]);
        // self.cs.borrow_mut().outputs.push(new)
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::target::smt::check_sat;

    fn bv_var(s: &str, w: usize) -> Term {
        leaf_term(Op::Var(s.to_owned(), Sort::BitVector(w)))
    }

    // #[test]
    // fn sat_test() {
    //     let cs = Rc::new(RefCell::new(Computation::new(false)));
    //     let mut mem = MemManager::new(cs.clone());
    //     let id0 = mem.zero_allocate(6, 4, 8);
    //     let _id1 = mem.zero_allocate(6, 4, 8);
    //     mem.store(id0, bv_lit(3, 4), bv_lit(2, 8));
    //     let a = mem.load(id0, bv_lit(3, 4));
    //     let b = mem.load(id0, bv_lit(1, 4));
    //     let t = term![Op::BvBinPred(BvBinPred::Ugt); a, b];
    //     cs.borrow_mut().assert(t);
    //     let sys = term(
    //         Op::BoolNaryOp(BoolNaryOp::And),
    //         cs.borrow().outputs().clone(),
    //     );
    //     assert!(check_sat(&sys))
    // }

    // #[test]
    // fn unsat_test() {
    //     let cs = Rc::new(RefCell::new(Computation::new(false)));
    //     let mut mem = MemManager::new(cs.clone());
    //     let id0 = mem.zero_allocate(6, 4, 8);
    //     let _id1 = mem.zero_allocate(6, 4, 8);
    //     mem.store(id0, bv_lit(3, 4), bv_var("a", 8));
    //     let a = mem.load(id0, bv_lit(3, 4));
    //     let b = mem.load(id0, bv_lit(3, 4));
    //     let t = term![Op::Not; term![Op::Eq; a, b]];
    //     cs.borrow_mut().assert(t);
    //     let sys = term(
    //         Op::BoolNaryOp(BoolNaryOp::And),
    //         cs.borrow().outputs().clone(),
    //     );
    //     assert!(!check_sat(&sys))
    // }
}
