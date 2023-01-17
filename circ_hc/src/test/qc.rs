use crate::{Node, Table};

pub fn leaf<T: Table<u8>>(u: u8) {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let n = T::create_ref(&u, std::iter::empty());
    assert_eq!(T::table_size(), 1);
    assert_eq!(n.op(), &u);
    assert_eq!(n.cs().len(), 0);
    std::mem::drop(n);
    let n_collected = T::gc();
    assert_eq!(n_collected, 1);
    assert_eq!(T::table_size(), 0);
}

pub fn four_nodes<T: Table<u8>>(a: u8, b: u8, c: u8, d: u8) {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let n_a = T::create_ref(&a, std::iter::empty());
    let n_b = T::create_ref(&b, [&n_a]);
    let n_c = T::create_ref(&c, [&n_a, &n_b]);
    let n_d = T::create_ref(&d, [&n_a, &n_b, &n_c]);
    assert_eq!(T::table_size(), 4);
    let n_d_2 = T::create_ref(&d, [&n_a, &n_b, &n_c]);
    assert_eq!(T::table_size(), 4);
    assert!(n_d == n_d_2);
    std::mem::drop(n_d_2);
    assert_eq!(T::gc(), 0);
    assert_eq!(T::table_size(), 4);
    std::mem::drop(n_d);
    assert_eq!(T::gc(), 1);
    std::mem::drop(n_b);
    assert_eq!(T::gc(), 0);
    std::mem::drop(n_a);
    std::mem::drop(n_c);
    T::gc();
    assert_eq!(T::table_size(), 0);
}

pub fn many_nodes<T: Table<u8>>(steps: Vec<(u8, Vec<usize>)>) {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let mut nodes = Vec::new();
    nodes.push(T::create_ref(&0, []));
    nodes.push(T::create_ref(&1, []));
    nodes.push(T::create_ref(&2, []));
    for (op, children) in steps {
        let node = T::create_ref(&op, children.into_iter().map(|i| &nodes[i % nodes.len()]));
        nodes.push(node);
    }
    assert!(T::table_size() > 2);
    for _ in 0..nodes.len() {
        nodes.pop();
        T::gc();
    }
    assert_eq!(T::table_size(), 0);
}
