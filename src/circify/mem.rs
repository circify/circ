use crate::ir::term::*;

use rug::Integer;

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

/// All-ones bv
fn ones(width: usize) -> Term {
    bv_lit((Integer::from(1) << width as u32) - 1, width)
}

/// Convert `t` to width `w`, though unsigned extension or extraction
fn to_width(t: &Term, w: usize) -> Term {
    let old_w = check(t).as_bv();
    if old_w < w {
        term![Op::BvUext(w - old_w); t.clone()]
    } else if old_w == w {
        t.clone()
    } else {
        term![Op::BvExtract(w - 1, 0); t.clone()]
    }
}

type AllocId = usize;

pub struct Alloc {
    id: AllocId,
    addr_width: usize,
    val_width: usize,
    cur_ver: usize,
    size: usize,
    cur_var: Term,
}

impl Alloc {
    /// Get the variable for the next version, and advance the next version.
    fn next_var(&mut self) {
        self.cur_ver += 1;
        let t = leaf_term(Op::Var(
            format!("mem_{}_v{}", self.id, self.cur_ver),
            self.sort(),
        ));
        self.cur_var = t;
    }

    fn sort(&self) -> Sort {
        Sort::Array(
            Box::new(Sort::BitVector(self.addr_width)),
            Box::new(Sort::BitVector(self.val_width)),
            self.size,
        )
    }

    fn new(id: AllocId, addr_width: usize, val_width: usize, size: usize) -> Self {
        Self {
            id,
            addr_width,
            val_width,
            size,
            cur_ver: 0,
            cur_var: leaf_term(Op::Var(
                format!("mem_{}_v{}", id, 0),
                Sort::Array(
                    Box::new(Sort::BitVector(addr_width)),
                    Box::new(Sort::BitVector(val_width)),
                    size,
                ),
            )),
        }
    }

    fn var(&self) -> &Term {
        &self.cur_var
    }
}

pub struct MemManager {
    allocs: HashMap<AllocId, Alloc>,
    next_id: usize,
    cs: Rc<RefCell<Constraints>>,
}

impl MemManager {
    pub fn new(cs: Rc<RefCell<Constraints>>) -> Self {
        Self {
            allocs: HashMap::new(),
            next_id: 0,
            cs,
        }
    }

    /// Returns the next allocation identifier, and advances it.
    fn take_next_id(&mut self) -> usize {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    fn assert(&mut self, t: Term) {
        debug_assert!(check(&t) == Sort::Bool);
        self.cs.borrow_mut().assertions.push(t);
    }

    pub fn allocate(&mut self, array: Term) -> AllocId {
        let s = check(&array);
        if let Sort::Array(box Sort::BitVector(addr_width), box Sort::BitVector(val_width), size) =
            s
        {
            let id = self.take_next_id();
            let alloc = Alloc::new(id, addr_width, val_width, size);
            let v = alloc.var().clone();
            if let Op::Var(n, _) = &v.op {
                self.cs.borrow_mut().eval_and_save(&n, &array);
            } else {
                unreachable!()
            }
            self.assert(term![Op::Eq; v, array]);
            self.allocs.insert(id, alloc);
            id
        } else {
            panic!("Cannot allocate array of sort: {}", s)
        }
    }

    pub fn zero_allocate(&mut self, size: usize, addr_width: usize, val_width: usize) -> AllocId {
        let sort = Sort::Array(
            Box::new(Sort::BitVector(addr_width)),
            Box::new(Sort::BitVector(val_width)),
            size,
        );
        let array = Value::Array(
            sort,
            Box::new(Value::BitVector(BitVector::zeros(val_width))),
            BTreeMap::new(),
            size,
        );
        self.allocate(leaf_term(Op::Const(array)))
    }

    pub fn load(&self, id: AllocId, offset: Term) -> Term {
        let alloc = self.allocs.get(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        term![Op::Select; alloc.var().clone(), offset]
    }

    pub fn store(&mut self, id: AllocId, offset: Term, val: Term) {
        let alloc = self.allocs.get_mut(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        assert_eq!(alloc.val_width, check(&val).as_bv());
        let new = term![Op::Store; alloc.var().clone(), offset, val];
        alloc.next_var();
        let v = alloc.var().clone();
        if let Op::Var(n, _) = &v.op {
            self.cs.borrow_mut().eval_and_save(&n, &new);
        } else {
            unreachable!()
        }
        self.assert(term![Op::Eq; v, new]);
    }

    pub fn in_bounds(&self, id: AllocId, offset: Term) -> Term {
        let alloc = self.allocs.get(&id).expect("Missing allocation");
        assert_eq!(alloc.addr_width, check(&offset).as_bv());
        term![Op::BvBinPred(BvBinPred::Ult); offset, bv_lit(alloc.size, alloc.addr_width)]
    }
}
