use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

use std::cell::{Cell, RefCell};
use std::hash::Hash;
use std::net::SocketAddrV6 as TemplateOp;
use std::thread_local;

const GC_IN_DROP_THRESH: usize = 5000;

#[derive(Clone)]
#[allow(dead_code)]
pub struct NodeData {
    pub op: TemplateOp,
    pub cs: Box<[Node]>,
}

pub struct Node {
    ptr: *const NodeValue,
}

#[allow(dead_code)]
pub fn create<'a>(op: &TemplateOp, children: impl IntoIterator<Item = &'a Node>) -> Node {
    MANAGER.with(|man| man.create(op, children))
}

#[allow(dead_code)]
pub fn gc() -> usize {
    MANAGER.with(|man| man.force_gc())
}

#[allow(dead_code)]
pub fn table_size() -> usize {
    MANAGER.with(|man| man.table.borrow().len())
}

struct NodeValue {
    raw: NodeData,
    id: u64,
    ref_cnt: Cell<u64>,
}

#[repr(transparent)]
struct NodeValuePtr(*const NodeValue);

struct Manager {
    table: RefCell<HashMap<NodeData, *const NodeValue>>,
    next_id: Cell<u64>,
    zombies: RefCell<HashSet<NodeValuePtr>>,
    in_gc: Cell<bool>,
}

thread_local! {
    static MANAGER: Manager = Manager {
        table: Default::default(),
        next_id: Cell::new(0),
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
    fn create<'a>(&self, op: &TemplateOp, children: impl IntoIterator<Item = &'a Node>) -> Node {
        #[allow(unused_unsafe)]
        unsafe {
            // TODO: hash w/o clone.
            let raw = NodeData {
                cs: children.into_iter().cloned().collect(),
                op: op.clone(),
            };
            let id = self.next_id.get();
            let ptr = {
                let mut table = self.table.borrow_mut();
                let value = table.entry(raw).or_insert_with_key(|raw| {
                    Box::into_raw(Box::new(NodeValue {
                        raw: raw.clone(),
                        id,
                        ref_cnt: Cell::new(0),
                    }))
                });
                NodeValue::inc(*value);
                if (**value).id == id {
                    self.next_id.set(id.checked_add(1).expect("id overflow"));
                }
                &**value as *const NodeValue
            };
            Node { ptr }
        }
    }

    fn remove_from_table(&self, ptr: NodeValuePtr) -> Box<NodeValue> {
        unsafe {
            let value_ptr = self.table.borrow_mut().remove(&(*ptr.0).raw).unwrap();
            Box::from_raw(value_ptr as *mut NodeValue)
        }
    }

    fn mark_for_deletion(&self, ptr: NodeValuePtr) {
        debug_assert_eq!(unsafe { (*ptr.0).ref_cnt.get() }, 0);
        self.zombies.borrow_mut().insert(ptr);
        if !self.in_gc.get() {
            if self.zombies.borrow().len() > GC_IN_DROP_THRESH {
                self.force_gc();
            }
        }
    }

    fn force_gc(&self) -> usize {
        // TODO: panic safety?
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
                    // TODO: attrs?
                    // drops the operator, then the children
                    // may create more zombies
                    std::mem::drop(value)
                }
            }
        }
        self.in_gc.set(false);
        ct
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

impl std::ops::Deref for Node {
    type Target = NodeData;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.ptr).raw }
    }
}

impl std::ops::Drop for Node {
    fn drop(&mut self) {
        NodeValue::dec(self.ptr)
    }
}

// 64 bit primes
const HASH_PRIME_1: u64 = 15124035408605323001;
const HASH_PRIME_2: u64 = 15133577374253939647;

impl Hash for NodeValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let id_hash = self
            .id
            .wrapping_mul(HASH_PRIME_1)
            .wrapping_add(HASH_PRIME_2);
        state.write_u64(id_hash);
    }
}

impl Hash for NodeData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        unsafe {
            for c in self.cs.iter() {
                (*c.ptr).hash(state);
            }
        }
    }
}

impl Hash for Node {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        use std::ops::Deref;
        self.deref().hash(state)
    }
}

impl Hash for NodeValuePtr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { (*self.0).hash(state) }
    }
}

impl PartialEq for NodeValue {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for NodeValue {}

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
        use std::ops::Deref;
        self.deref() == other.deref()
    }
}
impl Eq for Node {}

impl PartialEq for NodeValuePtr {
    fn eq(&self, other: &Self) -> bool {
        unsafe { *self.0 == *other.0 }
    }
}
impl Eq for NodeValuePtr {}
