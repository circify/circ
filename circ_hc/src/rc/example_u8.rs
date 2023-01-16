// Warning: this file is generated from src/template.rs and generate_u8.zsh
use fxhash::FxHashMap as HashMap;

use crate::Id;
use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::thread_local;

#[allow(dead_code)]
struct NodeData {
    op: u8,
    cs: Box<[Node]>,
}

struct NodeDataRef<'a, Q: Borrow<[Node]>>(&'a u8, &'a Q);

#[derive(Clone)]
pub struct Node {
    data: Rc<NodeData>,
    id: Id,
}

struct NodeListShallowDebug<'a>(&'a [Node]);

impl<'a> std::fmt::Debug for NodeListShallowDebug<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.0.iter().map(|n| &n.id))
            .finish()
    }
}

struct NodeShallowDebug<'a>(&'a Node);

impl<'a> std::fmt::Debug for NodeShallowDebug<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("id", &self.0.id)
            .field("rc", &Rc::strong_count(&self.0.data))
            .field("op", &self.0.data.op)
            .field("cs", &NodeListShallowDebug(&self.0.data.cs))
            .finish()
    }
}

pub struct Table {}

impl crate::Table<u8> for Table {
    type Node = Node;

    #[allow(dead_code)]
    fn create(op: &u8, children: Vec<Node>) -> Node {
        MANAGER.with(|man| man.create(op, children))
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
        "rc"
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

struct Manager {
    table: RefCell<HashMap<Rc<NodeData>, Node>>,
    next_id: Cell<Id>,
    gc_hook: RefCell<Option<Box<dyn Fn(Id) -> Vec<Node>>>>,
}

struct TableDebug<'a>(&'a HashMap<Rc<NodeData>, Node>);

impl<'a> std::fmt::Debug for TableDebug<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = f.debug_set();
        // Not using debug_set().entries(..) b/c it requires the entries to be long-lived.
        for n in self.0.values() {
            s.entry(&NodeShallowDebug(n));
        }
        s.finish()
    }
}

impl std::fmt::Debug for Manager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Manager")
            .field("table", &TableDebug(&*self.table.borrow()))
            .field("next_id", &self.next_id.get())
            .finish()
    }
}

thread_local! {
    static MANAGER: Manager = Manager {
        table: Default::default(),
        next_id: Cell::new(Id(0)),
        gc_hook: Default::default(),
    };
}

impl Node {
    fn try_unwrap(self) -> Result<NodeData, Self> {
        Rc::try_unwrap(self.data).map_err(|data| Node { data, id: self.id })
    }
}

impl Manager {
    fn create(&self, op: &u8, children: Vec<Node>) -> Node {
        let mut table = self.table.borrow_mut();
        let data = Rc::new(NodeData {
            op: op.clone(),
            cs: children.into(),
        });

        table
            .entry(data)
            .or_insert_with_key(|key| {
                let id = self.next_id.get();
                self.next_id
                    .set(Id(id.0.checked_add(1).expect("id overflow")));
                Node {
                    data: key.clone(),
                    id,
                }
            })
            .clone()
    }

    fn force_gc(&self) -> usize {
        let mut table = self.table.borrow_mut();
        let old_size = table.len();
        let mut to_collect: Vec<Node> = Vec::new();
        table.retain(|_, value| {
            if Rc::strong_count(&value.data) > 2 {
                true
            } else {
                to_collect.push(value.clone());
                false
            }
        });
        while let Some(t) = to_collect.pop() {
            let id = t.id;
            let data = Node::try_unwrap(t).unwrap_or_else(|node| {
                panic!(
                    "Attempting to collect node {:?}. but it has >1 ref",
                    NodeShallowDebug(&node)
                )
            });
            for c in data.cs.into_vec() {
                if Rc::strong_count(&c.data) <= 3 {
                    debug_assert_eq!(Rc::strong_count(&c.data), 3);
                    table.remove(&c.data);
                    to_collect.push(c.clone());
                }
            }
            if let Some(h) = self.gc_hook.borrow_mut().as_mut() {
                for c in h(id) {
                    if Rc::strong_count(&c.data) <= 3 {
                        debug_assert_eq!(Rc::strong_count(&c.data), 3);
                        table.remove(&c.data);
                        to_collect.push(c.clone());
                    }
                }
            }
        }
        let new_size = table.len();
        old_size - new_size
    }
}

impl crate::Node<u8> for Node {
    fn ref_cnt(&self) -> u64 {
        Rc::strong_count(&self.data) as u64
    }

    fn id(&self) -> Id {
        self.id
    }

    fn op(&self) -> &u8 {
        &self.data.op
    }

    fn cs(&self) -> &[Self] {
        &self.data.cs
    }

    type Weak = Weak;

    fn downgrade(&self) -> Self::Weak {
        Weak {
            data: Rc::downgrade(&self.data),
            id: self.id,
        }
    }
}

#[derive(Clone)]
pub struct Weak {
    data: std::rc::Weak<NodeData>,
    id: Id,
}

impl crate::Weak<u8> for Weak {
    type Node = Node;

    fn id(&self) -> Id {
        self.id
    }

    fn upgrade(&self) -> Option<Self::Node> {
        self.data.upgrade().map(|data| Node { data, id: self.id })
    }
}

mod hash {
    use super::{Node, NodeData, NodeDataRef, Weak};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    impl Hash for Node {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.id.hash(state)
        }
    }

    impl Hash for Weak {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.id.hash(state)
        }
    }

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
    use super::{Node, NodeData, Weak};
    use std::cmp::{Ord, PartialOrd};

    impl PartialEq for Node {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
    impl Eq for Node {}

    impl PartialOrd for Node {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Node {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.id.cmp(&other.id)
        }
    }

    impl PartialEq for Weak {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
    impl Eq for Weak {}

    impl PartialOrd for Weak {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Weak {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.id.cmp(&other.id)
        }
    }

    impl PartialEq for NodeData {
        fn eq(&self, other: &Self) -> bool {
            self.op == other.op
                && self.cs.len() == other.cs.len()
                && self.cs.iter().zip(other.cs.iter()).all(|(s, o)| s == o)
        }
    }
    impl Eq for NodeData {}
}
