use super::hc_u8;

#[test]
fn one() {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let n = hc_u8::create(&1, []);
    assert_eq!(hc_u8::table_size(), 1);
    std::mem::drop(n);
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
}

#[test]
fn two() {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let n = hc_u8::create(&1, []);
    let n2 = hc_u8::create(&1, [&n]);
    assert_eq!(hc_u8::table_size(), 2);
    std::mem::drop(n);
    std::mem::drop(n2);
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
}

#[test]
fn dup() {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let n = hc_u8::create(&1, []);
    let n2 = hc_u8::create(&1, [&n]);
    assert_eq!(hc_u8::table_size(), 2);
    let n3 = hc_u8::create(&1, [&n]);
    assert_eq!(hc_u8::table_size(), 2);
    std::mem::drop(n);
    hc_u8::gc();
    std::mem::drop(n2);
    std::mem::drop(n3);
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
}

#[test]
fn min() {
    let a = 0;
    let b = 0;
    let c = 0;
    let d = 0;
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
    assert_eq!(n_a.op, a);
    assert_eq!(n_b.op, b);
    assert_eq!(n_c.op, c);
    assert_eq!(n_d.op, d);
    std::mem::drop(n_d);
    std::mem::drop(n_c);
    std::mem::drop(n_b);
    std::mem::drop(n_a);
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
}

#[test]
fn nodrop() {
    hc_u8::gc();
    assert_eq!(hc_u8::table_size(), 0);
    let n = hc_u8::create(&1, []);
    assert_eq!(n.op, 1);
}
