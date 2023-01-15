#![feature(hash_raw_entry)]
use circ_hc::{Table as TableTrait, Node as NodeTrait, generate_hashcons};

generate_hashcons!(u32);

fn main() {
    let node = Table::create(&0, vec![]);
    assert!(node.op() == &0);
}
