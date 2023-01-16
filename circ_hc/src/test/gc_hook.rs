use crate::{Node, Table, Id};
use std::cell::RefCell;
use std::rc::Rc;
use std::collections::HashMap;

/// One step in the test.
#[derive(Debug)]
#[allow(dead_code)]
enum Step {
    New(u8, Vec<usize>),
    Del(usize),
    Dup(usize),
    Cache(usize, usize),
    Gc,
    AssertTableSize(usize),
    AssertCacheSize(usize),
}


fn test_seq<T: Table<u8>>(steps: &[Step]) {
    T::reserve(steps.len());
    let mut mem = vec![];
    let cache = Rc::new(RefCell::new(HashMap::<Id, T::Node>::default()));
    let cache2 = cache.clone();
    T::set_gc_hook(move |id| cache2.borrow_mut().remove(&id).into_iter().collect());
    for s in steps {
        println!("Step {:?}", s);
        match s {
            Step::New(t, args) => {
                let new_t = T::create_ref(t, args.iter().map(|i| &mem[*i]));
                mem.push(new_t);
            }
            Step::Dup(i) => {
                let prev = &mem[*i];
                let new_t = T::create_ref(prev.op(), prev.cs().iter());
                mem.push(new_t);
            }
            Step::Del(i) => {
                mem.remove(i % mem.len());
            }
            Step::Cache(k, v) => {
                cache.borrow_mut().insert(mem[k % mem.len()].id(), mem[v % mem.len()].clone());
            }
            Step::Gc => {
                T::gc();
            }
            Step::AssertTableSize(size) => {
                assert_eq!(*size, T::table_size());
            }
            Step::AssertCacheSize(size) => {
                assert_eq!(*size, cache.borrow().len());
            }
        }
    }
}

pub fn two<T: Table<u8>>() {
    test_seq::<T>(&[
        Step::New(0, vec![]),
        Step::New(1, vec![]),
        Step::AssertTableSize(2),
        Step::AssertCacheSize(0),
        Step::Cache(0, 1),
        Step::Del(1),
        Step::Gc,
        Step::AssertTableSize(2),
        Step::AssertCacheSize(1),
        Step::Del(0),
        Step::Gc,
        Step::AssertTableSize(0),
        Step::AssertCacheSize(0),
    ]);
}
