use circ_hc::{generate_hashcons_rc, Node as NodeTrait, Table as TableTrait};

generate_hashcons_rc!(u32);

fn main() {
    let node = Table::create(&0, vec![]);
    assert!(node.op() == &0);
}
