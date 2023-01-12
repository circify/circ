use quickcheck_macros::quickcheck;

use super::hc_u8;

#[quickcheck]
fn leaf(u: u8) {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let n = hc_u8::create(&u, std::iter::empty());
    assert_eq!(hc_u8::table_size(), 1);
    assert_eq!(n.op, u);
    assert_eq!(n.cs.len(), 0);
    std::mem::drop(n);
    let n_collected = hc_u8::gc();
    assert_eq!(n_collected, 1);
    assert_eq!(hc_u8::table_size(), 0);
}

#[quickcheck]
fn four_nodes(a: u8, b: u8, c: u8, d: u8) {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let n_a = hc_u8::create(&a, std::iter::empty());
    let n_b = hc_u8::create(&b, [&n_a]);
    let n_c = hc_u8::create(&c, [&n_a, &n_b]);
    let n_d = hc_u8::create(&d, [&n_a, &n_b, &n_c]);
    assert_eq!(hc_u8::table_size(), 4);
    let n_d_2 = hc_u8::create(&d, [&n_a, &n_b, &n_c]);
    assert_eq!(hc_u8::table_size(), 4);
    assert!(n_d == n_d_2);
    std::mem::drop(n_d_2);
    assert_eq!(hc_u8::gc(), 0);
    assert_eq!(hc_u8::table_size(), 4);
    std::mem::drop(n_d);
    assert_eq!(hc_u8::gc(), 1);
    std::mem::drop(n_b);
    assert_eq!(hc_u8::gc(), 0);
    std::mem::drop(n_a);
    std::mem::drop(n_c);
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn many_nodes(steps: Vec<(u8, Vec<usize>)>) {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let mut nodes = Vec::new();
    nodes.push(hc_u8::create(&0, []));
    nodes.push(hc_u8::create(&1, []));
    nodes.push(hc_u8::create(&2, []));
    for (op, children) in steps {
        let node = hc_u8::create(&op, children.into_iter().map(|i| &nodes[i % nodes.len()]));
        nodes.push(node);
    }
    assert!(hc_u8::table_size() > 2);
    for _ in 0..nodes.len() {
        nodes.pop();
        hc_u8::gc();
    }
    assert_eq!(hc_u8::table_size(), 0);
}
