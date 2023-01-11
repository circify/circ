use circ_hc::generate_hashcons;

generate_hashcons!(u32);

fn main() {
    let node = create(&0, std::iter::empty());
    assert!(node.op == 0);
}
