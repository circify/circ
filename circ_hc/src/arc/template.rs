use fxhash::FxHashMap as HashMap;

use hashconsing::*;

use crate::Id;
use std::borrow::Borrow;
use std::net::SocketAddrV6 as TemplateOp;
use std::sync::{Arc, RwLock};
use std::thread_local;

/// A (perfectly shared) pointer to a term
pub type Node = HConsed<NodeData>;
// "Temporary" terms.
/// A weak (perfectly shared) pointer to a term
pub type Weak = WHConsed<NodeData>;

struct NodeTable {
    map: HashMap<Arc<NodeData>, Weak>,
    gc_hook: Arc<RwLock<Option<Arc<dyn Fn(Id) -> Vec<Node>>>>>,
    count: u64,
    last_len: usize,
}

#[allow(dead_code)]
struct NodeData {
    op: TemplateOp,
    cs: Box<[Node]>,
}

impl NodeTable {
    fn get(&self, key: &NodeData) -> Option<Node> {
        if let Some(old) = self.map.get(key) {
            old.to_hconsed()
        } else {
            None
        }
    }
    fn mk(&mut self, elm: NodeData) -> Node {
        // If the element is known and upgradable return it.
        if let Some(hconsed) = self.get(&elm) {
            //debug_assert!(*hconsed.elm == elm);
            return hconsed;
        }
        // Otherwise build hconsed version.
        let elm = Arc::new(elm);
        let hconsed = HConsed {
            elm: elm.clone(),
            uid: self.count,
        };
        // Increment uid count.
        self.count += 1;
        // ...add weak version to the table...
        self.map.insert(elm, hconsed.to_weak());
        // ...and return consed version.
        hconsed
    }
    fn mk_ref(&mut self, elm: &NodeData) -> Node {
        // If the element is known and upgradable return it.
        if let Some(hconsed) = self.get(elm) {
            //debug_assert!(*hconsed.elm == elm);
            return hconsed;
        }
        // Otherwise build hconsed version.
        let elm = Arc::new(elm.clone());
        let hconsed = HConsed {
            elm: elm.clone(),
            uid: self.count,
        };
        // Increment uid count.
        self.count += 1;
        // ...add weak version to the table...
        self.map.insert(elm, hconsed.to_weak());
        // ...and return consed version.
        hconsed
    }
    fn collect(&mut self) {
        let mut table = &mut self.map;
        let mut to_collect: Vec<Node> = Vec::new();
        table.retain(|key, value| {
            if Arc::strong_count(key) > 2 {
                true
            } else {
                to_collect.push(HConsed {
                    elm: key.clone(),
                    uid: value.uid,
                });
                false
            }
        });
        while let Some(t) = to_collect.pop() {
            let uid = t.uid;
            let data = node_try_unwrap(t)
                .unwrap_or_else(|node| panic!("Attempting to collect node. but it has >1 ref",));
            for c in data.cs.into_vec() {
                if Arc::strong_count(&c.elm) <= 3 {
                    debug_assert_eq!(Arc::strong_count(&c.elm), 3);
                    table.remove(&c.elm);
                    to_collect.push(c.clone());
                }
            }
            if let Some(h) = self.gc_hook.borrow_mut().as_mut() {
                for c in h(Id(uid)) {
                    if Arc::strong_count(&c.elm) <= 3 {
                        debug_assert_eq!(Arc::strong_count(&c.elm), 3);
                        table.remove(&c.elm);
                        to_collect.push(c.clone());
                    }
                }
            }
        }
    }
}

pub struct Table;

impl crate::Table<TemplateOp> for Table {
    type Node = Node;
    type Weak = Weak;

    #[allow(dead_code)]
    fn create(op: &TemplateOp, children: Vec<Node>) -> Node {
        MANAGER.get_mut().mk(NodeData {
            op: op.clone(),
            cs: children.into(),
        })
    }

    #[allow(dead_code)]
    fn gc() -> usize {
        MANAGER.with(|man| man.force_gc())
    }

    #[allow(dead_code)]
    fn table_size() -> usize {
        MANAGER.with(|man| man.table.borrow().len())
    }

    fn name() -> &'static str {
        "arc"
    }

    fn reserve(num_nodes: usize) {
        MANAGER.with(|man| man.table.borrow_mut().reserve(num_nodes))
    }

    fn set_gc_hook(f: impl Fn(Id) -> Vec<Self::Node> + 'static) {
        MANAGER.with(|man| {
            let mut hook = man.gc_hook.borrow_mut();
            // don't assert that the hook is none, to allow it to be overwritten
            *hook = Some(Box::new(f));
        })
    }
}

static MANAGER: RwLock<NodeTable> = RwLock::new(NodeTable {
    map: Default::default(),
    gc_hook: Default::default(),
    count: 0,
    last_len: 0,
});

fn node_try_unwrap(n: Node) -> Result<NodeData, Node> {
    Arc::try_unwrap(n.elm).map_err(|elm| HConsed { elm, uid: n.uid })
}

impl crate::Node<TemplateOp> for Node {
    fn ref_cnt(&self) -> u64 {
        Arc::strong_count(&self.elm) as u64
    }

    fn id(&self) -> Id {
        Id(self.uid)
    }

    fn op(&self) -> &TemplateOp {
        &self.op
    }

    fn cs(&self) -> &[Self] {
        &self.cs
    }

    type Weak = Weak;

    fn downgrade(&self) -> Self::Weak {
        self.downgrade()
    }
}

impl crate::Weak<TemplateOp> for Weak {
    type Node = Node;

    fn id(&self) -> Id {
        Id(self.uid)
    }

    fn upgrade(&self) -> Option<Self::Node> {
        self.to_hconsed()
    }
}

mod hash {
    use super::{Node, NodeData, NodeDataRef};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    impl Hash for NodeData {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.op.hash(state);
            for c in self.cs.iter() {
                c.hash(state);
            }
        }
    }

    impl<'a, Q: Borrow<[Node]>> Hash for NodeDataRef<'a, Q> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.hash(state);
            for c in self.1.borrow().iter() {
                c.hash(state);
            }
        }
    }
}

mod cmp {
    use super::NodeData;

    impl PartialEq for NodeData {
        fn eq(&self, other: &Self) -> bool {
            self.op == other.op
                && self.cs.len() == other.cs.len()
                && self.cs.iter().zip(other.cs.iter()).all(|(s, o)| s == o)
        }
    }
    impl Eq for NodeData {}
}
