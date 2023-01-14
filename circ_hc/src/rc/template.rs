use fxhash::FxHashMap as HashMap;

use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::net::SocketAddrV6 as TemplateOp;
use std::rc::Rc;
use std::thread_local;

use crate::rc::once::OnceQueue;

#[allow(dead_code)]
pub struct NodeData {
    pub op: TemplateOp,
    pub cs: Box<[Node]>,
}

pub struct NodeDataRef<'a, Q: Borrow<[Node]>>(&'a TemplateOp, &'a Q);

impl<'a, Q: Borrow<[Node]>> NodeDataRef<'a, Q> {
    fn eq(&self, other: &Node) -> bool {
        use crate::Node;
        let cs = self.1.borrow();
        self.0 == other.op()
            && cs.len() == other.cs().len()
            && cs.iter().zip(other.cs().iter()).all(|(s, o)| s == o)
    }
}

#[derive(Clone)]
pub struct Node {
    data: Rc<NodeData>,
    id: u64,
}

pub struct Table {}

impl crate::Table<TemplateOp> for Table {
    type Node = Node;

    #[allow(dead_code)]
    fn create(op: &TemplateOp, children: Vec<Node>) -> Node {
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
}

struct Manager {
    table: RefCell<HashMap<Node, Node>>,
    next_id: Cell<u64>,
}

thread_local! {
    static MANAGER: Manager = Manager {
        table: Default::default(),
        next_id: Cell::new(0),
    };
}

impl Manager {
    fn create(&self, op: &TemplateOp, children: Vec<Node>) -> Node {
        let mut table = self.table.borrow_mut();
        let ref_ = NodeDataRef(op, &children);
        let hash = {
            use std::hash::{BuildHasher, Hash, Hasher};
            let mut hash_state = table.hasher().build_hasher();
            ref_.hash(&mut hash_state);
            hash_state.finish()
        };

        table.raw_entry_mut().from_hash(hash,|key| {
            ref_.eq(key)
        }).or_insert_with(|| {
            let id = self.next_id.get();
            let node = Node { data: Rc::new(NodeData { op: op.clone(), cs: children.into() }), id};
            self.next_id.set(id.checked_add(1).expect("id overflow"));
            (node.clone(), node)
        }).0.clone()
    }

    fn force_gc(&self) -> usize {
        let mut table = self.table.borrow_mut();
        let old_size = table.len();
        let mut to_check: OnceQueue<Node> = OnceQueue::new();
        table.retain(|_, value| {
            if Rc::strong_count(&value.data) > 2 {
                true
            } else {
                to_check.push(value.clone());
                false
            }
        });
        while let Some(t) = to_check.pop() {
            let okv = table.get_key_value(&t);
            std::mem::drop(t);
            if let Some((key, _)) = okv {
                if Rc::strong_count(&key.data) <= 2 {
                    to_check.extend(key.data.cs.iter().cloned());
                    let key = key.clone();
                    table.remove(&key);
                }
            }
        }
        let new_size = table.len();
        old_size - new_size
    }
}

impl crate::Node<TemplateOp> for Node {
    fn ref_cnt(&self) -> u64 {
        Rc::strong_count(&self.data) as u64
    }

    fn id(&self) -> u64 {
        self.id
    }

    fn op(&self) -> &TemplateOp {
        &self.data.op
    }

    fn cs(&self) -> &[Self] {
        &self.data.cs
    }
}

mod hash {
    use super::{Node, NodeData, NodeDataRef};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    // 64 bit primes
    const PRIME_1: u64 = 15124035408605323001;
    const PRIME_2: u64 = 15133577374253939647;

    impl Hash for Node {
        fn hash<H: Hasher>(&self, state: &mut H) {
            let id_hash = self.id.wrapping_mul(PRIME_1).wrapping_add(PRIME_2);
            state.write_u64(id_hash);
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
    use super::{Node, NodeData};
    use std::cmp::{Ord, PartialOrd};

    impl PartialEq for Node {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
    impl Eq for Node {}

    impl PartialEq for NodeData {
        fn eq(&self, other: &Self) -> bool {
            self.op == other.op
                && self.cs.len() == other.cs.len()
                && self.cs.iter().zip(other.cs.iter()).all(|(s, o)| s == o)
        }
    }
    impl Eq for NodeData {}

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
}
