// Warning: this file is generated from src/template.rs and generate_u8.zsh
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::thread_local;

use crate::Id;

const GC_IN_DROP_THRESH: f64 = 0.5;

#[derive(Clone)]
#[allow(dead_code)]
pub struct NodeData {
    pub op: u8,
    pub cs: Box<[Node]>,
}

pub struct Node {
    ptr: *const NodeValue,
}

pub struct Table {}

impl crate::Table<u8> for Table {
    type Node = Node;
    type Weak = Weak;

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
        "raw"
    }

    fn for_each(mut f: impl FnMut(&u8, &[Self::Node])) {
        MANAGER.with(|man| man.table.borrow().keys().for_each(|n| f(&n.op, &n.cs)));
    }

    fn reserve(num_nodes: usize) {
        MANAGER.with(|man| man.table.borrow_mut().reserve(num_nodes))
    }
}

struct NodeValue {
    raw: NodeData,
    id: Id,
    ref_cnt: Cell<u64>,
}

#[repr(transparent)]
struct NodeValuePtr(*const NodeValue);

struct Manager {
    table: RefCell<HashMap<NodeData, *const NodeValue>>,
    id_table: RefCell<HashMap<Id, *const NodeValue>>,
    next_id: Cell<Id>,
    attr_tables: RefCell<Vec<Rc<dyn attr::AttributeGc>>>,
    zombies: RefCell<HashSet<NodeValuePtr>>,
    in_gc: Cell<bool>,
}

thread_local! {
    static MANAGER: Manager = Manager {
        table: Default::default(),
        id_table: Default::default(),
        next_id: Cell::new(Id(0)),
        attr_tables: Default::default(),
        zombies: Default::default(),
        in_gc: Cell::new(false),
    };
}

impl NodeValue {
    fn dec(ptr: *const NodeValue) {
        unsafe {
            let ref_cnt = (*ptr).ref_cnt.get();
            debug_assert!(ref_cnt > 0);
            (*ptr).ref_cnt.set(ref_cnt - 1);
            if ref_cnt == 1 {
                MANAGER.with(|man| man.mark_for_deletion(NodeValuePtr(ptr)))
            }
        }
    }
    fn inc(ptr: *const NodeValue) {
        unsafe {
            let ref_cnt = (*ptr).ref_cnt.get();
            (*ptr)
                .ref_cnt
                .set(ref_cnt.checked_add(1).expect("ref_cnt overflow"));
        }
    }
}

impl Manager {
    fn create(&self, op: &u8, children: Vec<Node>) -> Node {
        #[allow(unused_unsafe)]
        unsafe {
            // TODO: hash w/o clone.
            let raw = NodeData {
                cs: children.into(),
                op: op.clone(),
            };
            let id = self.next_id.get();
            let ptr = {
                let mut table = self.table.borrow_mut();
                let mut existing = true;
                let value = table.entry(raw).or_insert_with_key(|raw| {
                    existing = false;
                    let ptr = Box::into_raw(Box::new(NodeValue {
                        raw: raw.clone(),
                        id,
                        ref_cnt: Cell::new(0),
                    }));
                    self.id_table.borrow_mut().insert(id, ptr);
                    ptr
                });
                NodeValue::inc(*value);
                if existing && (**value).ref_cnt.get() == 1 {
                    self.zombies.borrow_mut().remove(&NodeValuePtr(*value));
                }
                if (**value).id == id {
                    self.next_id
                        .set(Id(id.0.checked_add(1).expect("id overflow")));
                }
                &**value as *const NodeValue
            };
            Node { ptr }
        }
    }

    fn remove_from_table(&self, ptr: NodeValuePtr) -> Box<NodeValue> {
        unsafe {
            let id = (*ptr.0).id;
            debug_assert!(self.id_table.borrow_mut().remove(&id).is_some());
            let value_ptr = self.table.borrow_mut().remove(&(*ptr.0).raw).unwrap();
            Box::from_raw(value_ptr as *mut NodeValue)
        }
    }

    fn mark_for_deletion(&self, ptr: NodeValuePtr) {
        debug_assert_eq!(unsafe { (*ptr.0).ref_cnt.get() }, 0);
        let table_size = self.table.borrow().len();
        self.zombies.borrow_mut().insert(ptr);
        if !self.in_gc.get() {
            if self.zombies.borrow().len() as f64 > GC_IN_DROP_THRESH * table_size as f64 {
                self.force_gc();
            }
        }
    }

    fn force_gc(&self) -> usize {
        assert!(!self.in_gc.get(), "GC requested, but already in GC");
        self.in_gc.set(true);
        let mut ct = 0;
        loop {
            let zombies = self.zombies.take();
            if zombies.is_empty() {
                break;
            } else {
                for zombie in zombies {
                    ct += 1;
                    let value_box = self.remove_from_table(zombie);
                    let value = *value_box;

                    // attr GC
                    for t in self.attr_tables.borrow().iter() {
                        t.collect(value.id);
                    }

                    // drops the operator, then the children
                    // may create more zombies
                    std::mem::drop(value)
                }
            }
        }
        self.in_gc.set(false);
        ct
    }

    fn register_attr_table(&self, table: Rc<dyn attr::AttributeGc>) {
        self.attr_tables.borrow_mut().push(table)
    }
}

impl std::ops::Drop for Manager {
    fn drop(&mut self) {
        self.force_gc();
    }
}

impl Clone for Node {
    fn clone(&self) -> Self {
        NodeValue::inc(self.ptr);
        Self { ptr: self.ptr }
    }
}

impl crate::Node<u8> for Node {
    type Weak = Weak;

    fn ref_cnt(&self) -> u64 {
        unsafe { (*self.ptr).ref_cnt.get() }
    }

    fn id(&self) -> Id {
        unsafe { (*self.ptr).id }
    }

    fn op(&self) -> &u8 {
        unsafe { &(*self.ptr).raw.op }
    }

    fn cs(&self) -> &[Self] {
        unsafe { &(*self.ptr).raw.cs }
    }

    fn downgrade(&self) -> Self::Weak {
        Weak(self.id())
    }
}

impl std::ops::Drop for Node {
    fn drop(&mut self) {
        NodeValue::dec(self.ptr)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Weak(Id);

impl crate::Weak<u8> for Weak {
    type Node = Node;

    fn id(&self) -> Id {
        self.0
    }

    fn upgrade(&self) -> Option<Self::Node> {
        MANAGER.with(|man| {
            man.id_table.borrow().get(&self.id()).map(|ptr| {
                NodeValue::inc(*ptr);
                Node { ptr: *ptr }
            })
        })
    }
}

mod hash {
    use super::{Node, NodeData, NodeValue, NodeValuePtr};
    use std::hash::{Hash, Hasher};

    impl Hash for NodeValue {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.id.hash(state);
        }
    }

    impl Hash for NodeData {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.op.hash(state);
            unsafe {
                for c in self.cs.iter() {
                    (*c.ptr).hash(state);
                }
            }
        }
    }

    impl Hash for Node {
        fn hash<H: Hasher>(&self, state: &mut H) {
            unsafe { (*self.ptr).hash(state) }
        }
    }

    impl Hash for NodeValuePtr {
        fn hash<H: Hasher>(&self, state: &mut H) {
            unsafe { (*self.0).hash(state) }
        }
    }

    impl PartialEq for NodeValue {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
}

mod cmp {
    use super::{Node, NodeData, NodeValuePtr};
    use std::cmp::{Ord, PartialOrd};

    impl PartialEq for NodeData {
        fn eq(&self, other: &Self) -> bool {
            unsafe {
                self.op == other.op
                    && self.cs.len() == other.cs.len()
                    && self
                        .cs
                        .iter()
                        .zip(other.cs.iter())
                        .all(|(s, o)| *(s.ptr) == *(o.ptr))
            }
        }
    }
    impl Eq for NodeData {}

    impl PartialEq for Node {
        fn eq(&self, other: &Self) -> bool {
            unsafe { (*self.ptr).id == (*other.ptr).id }
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
            unsafe { (*self.ptr).id.cmp(&(*other.ptr).id) }
        }
    }

    impl PartialEq for NodeValuePtr {
        fn eq(&self, other: &Self) -> bool {
            unsafe { (*self.0).id == (*other.0).id }
        }
    }
    impl Eq for NodeValuePtr {}
}

/// Attribute tables
pub mod attr {
    use super::*;

    pub struct AttributeTable<T: 'static + Clone> {
        inner: Rc<AttributeTableInner<T>>,
    }

    // should not be moved
    pub struct AttributeTableInner<T: 'static> {
        table: RefCell<HashMap<Id, T>>,
    }

    pub trait AttributeGc {
        fn collect(&self, id: Id);
    }

    impl<T> AttributeGc for AttributeTableInner<T> {
        fn collect(&self, id: Id) {
            self.table.borrow_mut().remove(&id);
        }
    }

    impl<T: 'static + Clone> std::default::Default for AttributeTable<T> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T: 'static + Clone> AttributeTable<T> {
        /// Create an empty [AttributeTable].
        #[allow(dead_code)]
        pub fn new() -> Self {
            let inner = Rc::new(AttributeTableInner {
                table: Default::default(),
            });
            let cp = inner.clone();
            MANAGER.with(|man| man.register_attr_table(cp));
            AttributeTable { inner }
        }

        #[allow(dead_code)]
        pub fn len(&self) -> usize {
            self.inner.table.borrow().len()
        }

        #[allow(dead_code)]
        pub fn get(&self, k: &Node) -> Option<T> {
            use crate::Node;
            self.inner.table.borrow().get(&k.id()).cloned()
        }

        #[allow(dead_code)]
        pub fn insert(&mut self, k: &Node, v: T) -> Option<T> {
            use crate::Node;
            self.inner.table.borrow_mut().insert(k.id(), v)
        }
    }
}
