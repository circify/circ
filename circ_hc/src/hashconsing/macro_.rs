// Warning: this file is generated from src/hashconsing/template.rs and generate_macro.zsh
#[macro_export]
macro_rules! generate_hashcons_hashconsing {
    ($Op:ty) => {
        use hashconsing::*;
        use hashconsing::{HConsed, HashConsign};

        use $crate::Id;

        pub type Node = HConsed<ActualNode>;
        pub type Weak = WHConsed<ActualNode>;

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
            type Weak = Weak;

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

            fn name() -> &'static str {
                "hashconsing"
            }

            fn for_each(f: impl FnMut(&$Op, &[Self::Node])) {
                panic!()
            }

            fn reserve(num_nodes: usize) {
                FACTORY.reserve(num_nodes);
            }
        }

        impl $crate::Node<$Op> for Node {
            type Weak = Weak;

            fn ref_cnt(&self) -> u64 {
                self.arc_count() as u64
            }

            fn id(&self) -> Id {
                Id(self.uid())
            }

            fn op(&self) -> &$Op {
                &self.op
            }

            fn cs(&self) -> &[Self] {
                &self.cs
            }

            fn downgrade(&self) -> Self::Weak {
                self.to_weak()
            }
        }

        impl $crate::Weak<$Op> for Weak {
            type Node = Node;

            fn id(&self) -> Id {
                Id(self.uid)
            }

            fn live(&self) -> bool {
                std::sync::Weak::strong_count(&self.elm) > 0
            }

            fn upgrade(&self) -> Option<Self::Node> {
                self.to_hconsed()
            }
        }
    };
}
pub use crate::generate_hashcons_hashconsing as generate_hashcons;
