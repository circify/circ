use hashconsing::*;

use std::net::SocketAddrV6 as TemplateOp;

use hashconsing::{HConsed, HashConsign};
pub type Node = HConsed<ActualNode>;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ActualNode {
    op: TemplateOp,
    cs: Vec<Node>,
}

consign! {
    /// Factory for terms.
    let FACTORY = consign(37) for ActualNode ;
}

pub struct Table {}

impl crate::Table<TemplateOp> for Table {
    type Node = Node;

    #[allow(dead_code)]
    fn create<'a>(op: &TemplateOp, children: impl IntoIterator<Item = &'a Node>) -> Node {
        FACTORY.mk(ActualNode { op: op.clone(), cs: children.into_iter().cloned().collect() })
    }

    #[allow(dead_code)]
    fn gc() -> usize {
        let init_len = Table::table_size();
        FACTORY.collect();
        let final_len = Table::table_size();
        init_len - final_len
    }

    #[allow(dead_code)]
    fn table_size() -> usize {
        FACTORY.read().map(|f| f.len()).unwrap_or(0)
    }
}

impl crate::Node<TemplateOp> for Node {
    fn ref_cnt(&self) -> u64 {
        self.arc_count() as u64
    }

    fn id(&self) -> u64 {
        self.uid()
    }

    fn op(&self) -> &TemplateOp {
        &self.op
    }

    fn cs(&self) -> &[Self] {
        &self.cs
    }
}
