use crate::{Node, Table};

pub fn one<T: Table<u8>>() {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let n = T::create_ref(&1, []);
    assert_eq!(T::table_size(), 1);
    std::mem::drop(n);
    assert_eq!(1, T::gc());
    assert_eq!(T::table_size(), 0);
}

pub fn two<T: Table<u8>>() {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let n = T::create_ref(&1, []);
    let n2 = T::create_ref(&1, [&n]);
    assert_eq!(T::table_size(), 2);
    std::mem::drop(n);
    std::mem::drop(n2);
    T::gc();
    assert_eq!(T::table_size(), 0);
}

pub fn dup<T: Table<u8>>() {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let n = T::create_ref(&1, []);
    let n2 = T::create_ref(&1, [&n]);
    assert_eq!(T::table_size(), 2);
    let n3 = T::create_ref(&1, [&n]);
    assert_eq!(T::table_size(), 2);
    std::mem::drop(n);
    T::gc();
    std::mem::drop(n2);
    std::mem::drop(n3);
    T::gc();
    assert_eq!(T::table_size(), 0);
}

pub fn min<T: Table<u8>>() {
    let a = 0;
    let b = 0;
    let c = 0;
    let d = 0;
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
    assert_eq!(n_a.op(), &a);
    assert_eq!(n_b.op(), &b);
    assert_eq!(n_c.op(), &c);
    assert_eq!(n_d.op(), &d);
    std::mem::drop(n_d);
    std::mem::drop(n_c);
    std::mem::drop(n_b);
    std::mem::drop(n_a);
    T::gc();
    assert_eq!(T::table_size(), 0);
}

pub fn nodrop<T: Table<u8>>() {
    T::gc();
    assert_eq!(T::table_size(), 0);
    let n = T::create_ref(&1, []);
    assert_eq!(n.op(), &1);
}
