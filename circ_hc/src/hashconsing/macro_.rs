// Warning: this file is generated from src/hashconsing/template.rs and generate_macro.zsh
#[macro_export]
macro_rules! generate_hashcons_hashconsing {
    ($Op:ty) => {
        use hashconsing::*;

        use hashconsing::{HConsed, HashConsign};
        pub type Node = HConsed<ActualNode>;

        #[derive(Debug, Hash, Clone, PartialEq, Eq)]
        pub struct ActualNode {
            op: $Op,
            cs: Vec<Node>,
        }

        consign! {
            /// Factory for terms.
            let FACTORY = consign(37) for ActualNode ;
        }

        pub struct Table {}

        impl $crate::Table<$Op> for Table {
            type Node = Node;

            #[allow(dead_code)]
            fn create(op: &$Op, children: Vec<Node>) -> Node {
                FACTORY.mk(ActualNode {
                    op: op.clone(),
                    cs: children,
                })
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

        impl $crate::Node<$Op> for Node {
            fn ref_cnt(&self) -> u64 {
                self.arc_count() as u64
            }

            fn id(&self) -> u64 {
                self.uid()
            }

            fn op(&self) -> &$Op {
                &self.op
            }

            fn cs(&self) -> &[Self] {
                &self.cs
            }
        }
    };
}
pub use crate::generate_hashcons_hashconsing as generate_hashcons;
