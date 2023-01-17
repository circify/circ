use crate::{Id, Node, Table};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// One step in the test.
#[derive(Debug)]
#[allow(dead_code)]
enum Step {
    New(u8, Vec<usize>),
    Del(usize),
    Dup(usize),
    CacheNode(usize, usize),
    CacheScalar(usize, u8),
    Gc,
    AssertTableSize(usize),
    AssertCacheSize(usize),
}

fn test_seq<T: Table<u8>>(steps: &[Step]) {
    T::reserve(steps.len());
    let mut mem = vec![];
    let cache = Rc::new(RefCell::new(HashMap::<Id, T::Node>::default()));
    let scalar_cache = Rc::new(RefCell::new(HashMap::<Id, u8>::default()));
    let cache2 = cache.clone();
    let scalar_cache2 = scalar_cache.clone();
    // in case a previous test panic'd
    T::gc_hooks_clear();
    T::gc_hook_add("test", move |id| {
        scalar_cache2.borrow_mut().remove(&id);
        cache2.borrow_mut().remove(&id).into_iter().collect()
    });
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
            Step::CacheNode(k, v) => {
                cache
                    .borrow_mut()
                    .insert(mem[k % mem.len()].id(), mem[v % mem.len()].clone());
            }
            Step::CacheScalar(k, v) => {
                scalar_cache
                    .borrow_mut()
                    .insert(mem[k % mem.len()].id(), *v);
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
    T::gc_hook_remove("test");
}

pub fn two<T: Table<u8>>() {
    test_seq::<T>(&[
        Step::New(0, vec![]),
        Step::New(1, vec![]),
        Step::AssertTableSize(2),
        Step::AssertCacheSize(0),
        Step::CacheNode(0, 1),
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

pub fn three<T: Table<u8>>() {
    // cache pts to first child
    test_seq::<T>(&[
        Step::New(0, vec![]),
        Step::New(1, vec![0]),
        Step::New(2, vec![0, 1]),
        Step::AssertTableSize(3),
        Step::AssertCacheSize(0),
        Step::CacheNode(2, 0),
        Step::CacheNode(1, 0),
        Step::AssertCacheSize(2),
        Step::Gc,
        Step::AssertTableSize(3),
        Step::AssertCacheSize(2),
        Step::Del(2),
        Step::Gc,
        Step::AssertCacheSize(1),
        Step::AssertTableSize(2),
        Step::Del(0),
        Step::Gc,
        Step::AssertCacheSize(1),
        Step::AssertTableSize(2),
        Step::Del(0),
        Step::Gc,
        Step::AssertTableSize(0),
        Step::AssertCacheSize(0),
    ]);
}
