use fxhash::FxHashMap as HashMap;

use crate::Id;
use log::trace;
use std::borrow::Borrow;
use std::cell::{Cell, RefCell};
use std::net::SocketAddrV6 as TemplateOp;
use std::rc::Rc;
use std::thread_local;

#[allow(dead_code)]
struct NodeData {
    op: TemplateOp,
    cs: Box<[Node]>,
}

struct NodeDataRef<'a, Q: Borrow<[Node]>>(&'a TemplateOp, &'a Q);

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

impl crate::Table<TemplateOp> for Table {
    type Node = Node;
    type Weak = Weak;

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

    fn name() -> &'static str {
        "rc"
    }

    fn for_each(mut f: impl FnMut(&TemplateOp, &[Self::Node])) {
        MANAGER.with(|man| man.table.borrow().keys().for_each(|n| f(&n.op, &n.cs)));
    }

    fn reserve(num_nodes: usize) {
        MANAGER.with(|man| man.table.borrow_mut().reserve(num_nodes))
    }

    fn gc_hook_add(name: &'static str, f: impl Fn(Id) -> Vec<Self::Node> + 'static) {
        MANAGER.with(|man| {
            let mut hooks = man.gc_hooks.borrow_mut();
            let name = name.to_owned();
            assert!(!hooks.0.contains(&name), "Already a hook for '{}'", name);
            hooks.0.push(name);
            hooks.1.push(Box::new(f));
        })
    }
    // false positive on hooks!
    #[allow(unused_must_use)]
    fn gc_hook_remove(name: &'static str) {
        MANAGER.with(|man| {
            let mut hooks = man.gc_hooks.borrow_mut();
            let i = hooks
                .0
                .iter()
                .position(|n| n == name)
                .unwrap_or_else(|| panic!("No hook for '{}' to remove", name));
            hooks.0.remove(i);
            hooks.1.remove(i);
        })
    }
    fn gc_hooks_clear() {
        MANAGER.with(|man| {
            let mut hooks = man.gc_hooks.borrow_mut();
            hooks.0.clear();
            hooks.1.clear();
        })
    }
}

struct Manager {
    table: RefCell<HashMap<Rc<NodeData>, Node>>,
    /// Elements that are still in `table`, but should be collected.
    to_collect: RefCell<Vec<Weak>>,
    in_gc: Cell<bool>,
    next_id: Cell<Id>,
    /// a Vec map from [String] to function
    gc_hooks: RefCell<(Vec<String>, Vec<Box<dyn Fn(Id) -> Vec<Node>>>)>,
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
        to_collect: Default::default(),
        in_gc: Cell::new(false),
        next_id: Cell::new(Id(0)),
        gc_hooks: Default::default(),
    };
}

impl Manager {
    fn create(&self, op: &TemplateOp, children: Vec<Node>) -> Node {
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
        if !std::thread::panicking() {
            let start = std::time::Instant::now();
            assert!(!self.in_gc.get(), "Double GC");
            self.in_gc.set(true);
            let mut table = self.table.borrow_mut();
            let mut to_collect = self.to_collect.borrow_mut();
            let mut gc_hooks = self.gc_hooks.borrow_mut();
            let mut collected = 0;
            while let Some(t) = to_collect.pop() {
                collected += 1;
                let id = t.id;
                if t.data.strong_count() != 2 {
                    continue;
                }
                let strong_data = t.data.upgrade().expect("missing from table");
                table.remove(&strong_data).expect("missing from table");
                let data = Rc::try_unwrap(strong_data).unwrap_or_else(|d| {
                    panic!("to many refs to {:?}", NodeListShallowDebug(&d.cs))
                });
                for c in data.cs.into_vec() {
                    // 3 pointers: 2 from table, and this vector.
                    if Rc::strong_count(&c.data) <= 3 {
                        debug_assert_eq!(Rc::strong_count(&c.data), 3);
                        use crate::Node;
                        to_collect.push(c.downgrade());
                    }
                }
                for h in gc_hooks.1.iter_mut() {
                    for c in h(id) {
                        // 3 pointers: 2 from table, and this vector.
                        if Rc::strong_count(&c.data) <= 3 {
                            debug_assert_eq!(Rc::strong_count(&c.data), 3);
                            use crate::Node;
                            to_collect.push(c.downgrade());
                        }
                    }
                }
            }
            let new_size = table.len();
            let duration = start.elapsed();
            self.in_gc.set(false);
            trace!(
                "GC: {} terms -> {} terms in {} us",
                collected,
                new_size,
                duration.as_micros()
            );
            collected
        } else {
            0
        }
    }
}

impl crate::Node<TemplateOp> for Node {
    fn ref_cnt(&self) -> u64 {
        Rc::strong_count(&self.data) as u64
    }

    fn id(&self) -> Id {
        self.id
    }

    fn op(&self) -> &TemplateOp {
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

impl Drop for Node {
    fn drop(&mut self) {
        use crate::Node;
        // 3 pointers: 2 from table, and this one.
        if self.ref_cnt() <= 3 && !std::thread::panicking() {
            MANAGER
                .try_with(|m| {
                    if !m.in_gc.get() {
                        m.to_collect.borrow_mut().push(self.downgrade());
                    }
                })
                .ok();
        }
    }
}

#[derive(Clone)]
pub struct Weak {
    data: std::rc::Weak<NodeData>,
    id: Id,
}

impl crate::Weak<TemplateOp> for Weak {
    type Node = Node;

    fn id(&self) -> Id {
        self.id
    }

    fn live(&self) -> bool {
        std::rc::Weak::strong_count(&self.data) > 0
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

impl std::ops::Drop for Manager {
    fn drop(&mut self) {
        // If we just drop everything in the table, there can be deep Rc::drop recursions.
        //
        // If we run GC, then hopefully we avoid that.
        //
        // However, running GC takes a long time. This could probably be improved.
        if !std::thread::panicking() {
            self.force_gc();
        }
    }
}
