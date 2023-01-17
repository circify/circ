use crate::{Node, Table};

/// One step in the test.
#[derive(Debug)]
#[allow(dead_code)]
enum Step {
    New(u8, Vec<usize>),
    Del(usize),
    Weak(usize),
    Gc,
    AssertTableSize(usize),
}

fn test_seq<T: Table<u8>>(steps: &[Step]) {
    T::reserve(steps.len());
    let mut nodes = vec![];
    let mut weaks = vec![];
    for s in steps {
        println!("Step {:?}", s);
        match s {
            Step::New(t, args) => {
                let new_t = T::create_ref(t, args.iter().map(|i| &nodes[*i]));
                nodes.push(new_t);
            }
            Step::Weak(i) => {
                weaks.push(nodes[*i % nodes.len()].downgrade());
            }
            Step::Del(i) => {
                nodes.remove(i % nodes.len());
            }
            Step::Gc => {
                T::gc();
            }
            Step::AssertTableSize(size) => {
                assert_eq!(*size, T::table_size());
            }
        }
    }
}

pub fn two<T: Table<u8>>() {
    test_seq::<T>(&[
        Step::New(0, vec![]),
        Step::New(1, vec![]),
        Step::Weak(0),
        Step::Weak(1),
        Step::AssertTableSize(2),
        Step::Del(1),
        Step::Gc,
        Step::AssertTableSize(1),
        Step::Del(0),
        Step::Gc,
        Step::AssertTableSize(0),
    ]);
}

pub fn three<T: Table<u8>>() {
    // cache pts to first child
    test_seq::<T>(&[
        Step::New(0, vec![]),
        Step::New(1, vec![0]),
        Step::New(2, vec![0, 1]),
        Step::Weak(2),
        Step::Gc,
        Step::AssertTableSize(3),
        Step::Del(2),
        Step::Gc,
        Step::AssertTableSize(2),
        Step::Del(1),
        Step::Del(0),
        Step::Gc,
        Step::AssertTableSize(0),
    ]);
}
