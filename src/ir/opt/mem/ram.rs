/// RAM extraction.
///
/// The [volatile] module extracts volatile (intra-proof) RAMs, while the [persistent] module
/// extracts persistent (inter-proof) RAMs.
///
/// See the documentation for [volatile]
use log::trace;

use std::collections::VecDeque;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;
use circ_fields::FieldT;
use circ_opt::RamOpt;

mod checker;
mod hash;
pub mod persistent;
pub mod volatile;

#[derive(Debug)]
/// An access to a RAM
///
/// ## Field ordering
///
struct Access {
    /// The value read or (conditionally) written.
    pub val: Term,
    /// The index/address.
    pub idx: Term,
    /// The time of this access.
    pub time: Term,
    /// Whether this is a read or a write.
    pub write: FieldBit,
    /// Whether this initializes the index (always unset for reads).
    ///
    /// This field is meaningless if [AccessCfg::create] is unset.
    pub create: FieldBit,
    /// Whether this is active (always set for reads).
    pub active: FieldBit,
}

/// Let the fields be (v, i, t, w, c, a). We use two different field orderings.
///
/// The *hash* ordering is lexicographic by (v, i, t, w, c, a). We use it to evaluate a UHF (so v
/// is the constant in the UHF's polynomial).
///
/// The *sort* ordering is lexicographic by (i, t, a, v, w, c). We use this ordering to sort tuples
/// (and declare accesses).
#[derive(Clone, Copy)]
pub enum Order {
    /// Put non-constants first.
    Hash,
    /// The order of a sorted transcript.
    Sort,
}

#[derive(Debug, Clone)]
/// Contains access configuration (field & whether a create flag is present)
/// as well as cached terms.
pub struct AccessCfg {
    false_: Term,
    true_: Term,
    one: Term,
    zero: Term,
    field: FieldT,
    create: bool,
    sort_indices: bool,
    split_times: bool,
}

impl AccessCfg {
    /// Create a new configuration
    pub fn new(field: FieldT, opt: RamOpt, create: bool) -> Self {
        use circ_opt::{IndexStrategy, RangeStrategy};
        Self {
            false_: bool_lit(false),
            true_: bool_lit(true),
            one: pf_lit(field.new_v(1)),
            zero: pf_lit(field.new_v(0)),
            field,
            create,
            sort_indices: opt.index == IndexStrategy::Sort,
            split_times: opt.range == RangeStrategy::BitSplit,
        }
    }
    /// Create a default configuration, with this field.
    pub fn default_from_field(field: FieldT) -> Self {
        Self {
            false_: bool_lit(false),
            true_: bool_lit(true),
            one: pf_lit(field.new_v(1)),
            zero: pf_lit(field.new_v(0)),
            field,
            create: false,
            sort_indices: false,
            split_times: false,
        }
    }
    /// Create a new default configuration
    pub fn from_cfg() -> Self {
        Self::new(
            crate::cfg::cfg().field().clone(),
            crate::cfg::cfg().ram.clone(),
            true,
        )
    }
    fn len(&self) -> usize {
        if self.create {
            6
        } else {
            5
        }
    }
    fn bool2pf(&self, t: Term) -> Term {
        term![Op::Ite; t, self.one.clone(), self.zero.clone()]
    }
    fn pf_neg(&self, t: Term) -> Term {
        term![PF_ADD; self.one.clone(), term![PF_NEG; t]]
    }
}

/// A bit encoded in the field.
#[derive(Debug)]
struct FieldBit {
    /// The field value (0 or 1)
    f: Term,
    /// The negate field value (1 or 0)
    nf: Term,
    /// The bit value (false or true)
    b: Term,
}

impl FieldBit {
    fn from_bool_lit(c: &AccessCfg, b: bool) -> Self {
        Self {
            b: if b { c.true_.clone() } else { c.false_.clone() },
            f: if b { c.one.clone() } else { c.zero.clone() },
            nf: if b { c.zero.clone() } else { c.one.clone() },
        }
    }
    fn from_bool(c: &AccessCfg, b: Term) -> Self {
        debug_assert!(matches!(check(&b), Sort::Bool));
        Self {
            f: c.bool2pf(b.clone()),
            nf: c.bool2pf(term![NOT; b.clone()]),
            b,
        }
    }
    fn from_trusted_field(c: &AccessCfg, f: Term) -> Self {
        Self {
            b: term![Op::PfToBoolTrusted; f.clone()],
            nf: c.pf_neg(f.clone()),
            f,
        }
    }
}

impl Access {
    fn new_read(f: &AccessCfg, idx: Term, val: Term, time: Term) -> Self {
        Self {
            val,
            idx,
            time,
            write: FieldBit::from_bool_lit(f, false),
            active: FieldBit::from_bool_lit(f, true),
            create: FieldBit::from_bool_lit(f, false),
        }
    }
    fn new_write(f: &AccessCfg, idx: Term, val: Term, active: Term, time: Term) -> Self {
        Self {
            val,
            idx,
            time,
            write: FieldBit::from_bool_lit(f, true),
            active: FieldBit::from_bool(f, active),
            create: FieldBit::from_bool_lit(f, false),
        }
    }
    fn new_init(f: &AccessCfg, idx: Term, val: Term) -> Self {
        Self {
            val,
            idx,
            time: f.zero.clone(),
            write: FieldBit::from_bool_lit(f, true),
            active: FieldBit::from_bool_lit(f, true),
            create: FieldBit::from_bool_lit(f, true),
        }
    }

    fn field_names(c: &AccessCfg, order: Order) -> &'static [&'static str] {
        match order {
            Order::Hash => {
                if c.create {
                    &["v", "i", "t", "w", "a", "c"]
                } else {
                    &["v", "i", "t", "w", "a"]
                }
            }
            // dead code, but for clarity...
            Order::Sort => {
                if c.create {
                    &["i", "t", "c", "v", "w", "a"]
                } else {
                    &["i", "t", "v", "w", "a"]
                }
            }
        }
    }

    fn to_field_elems(&self, c: &AccessCfg, order: Order) -> Vec<Term> {
        match order {
            Order::Hash => {
                let mut out = vec![
                    self.val.clone(),
                    self.idx.clone(),
                    self.time.clone(),
                    self.write.f.clone(),
                    self.active.f.clone(),
                ];
                if c.create {
                    out.push(self.create.f.clone())
                }
                out
            }
            Order::Sort => {
                let mut out = vec![self.idx.clone(), self.time.clone()];
                if c.create {
                    out.push(self.create.f.clone())
                }
                out.push(self.val.clone());
                out.push(self.write.f.clone());
                out.push(self.active.f.clone());
                out
            }
        }
    }

    fn from_field_elems_trusted(elems: Vec<Term>, c: &AccessCfg, order: Order) -> Self {
        debug_assert_eq!(elems.len(), c.len());
        let mut elems = elems.into_iter();
        let mut next = || {
            let t = elems.next().unwrap();
            debug_assert!(matches!(check(&t), Sort::Field(_)));
            t
        };
        match order {
            Order::Hash => Self {
                val: next(),
                idx: next(),
                time: next(),
                write: FieldBit::from_trusted_field(c, next()),
                active: FieldBit::from_trusted_field(c, next()),
                create: if c.create {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    FieldBit::from_bool_lit(c, false)
                },
            },
            Order::Sort => Self {
                idx: next(),
                time: next(),
                create: if c.create {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    FieldBit::from_bool_lit(c, false)
                },
                val: next(),
                write: FieldBit::from_trusted_field(c, next()),
                active: FieldBit::from_trusted_field(c, next()),
            },
        }
    }

    fn universal_hash(&self, c: &AccessCfg, hasher: &hash::UniversalHasher) -> Term {
        assert_eq!(hasher.len(), c.len());
        hasher.hash(self.to_field_elems(c, Order::Hash))
    }

    fn to_field_tuple(&self, c: &AccessCfg) -> Term {
        term(Op::Tuple, self.to_field_elems(c, Order::Sort))
    }

    fn declare_trusted(
        c: &AccessCfg,
        mut declare_var: impl FnMut(&str, Term) -> Term,
        value_tuple: Term,
    ) -> Self {
        let mut declare_field =
            |name: &str, idx: usize| declare_var(name, term![Op::Field(idx); value_tuple.clone()]);
        let elems = Self::field_names(c, Order::Sort)
            .iter()
            .enumerate()
            .map(|(idx, name)| declare_field(name, idx))
            .collect();
        Self::from_field_elems_trusted(elems, c, Order::Sort)
    }
}

/// Constraints on the initial and final state of a RAM
#[derive(Debug)]
pub enum BoundaryConditions {
    /// An explicit enumeration of the initial and final values.
    Persistent(Vec<Term>, Vec<Term>),
    /// The initial values are all this.
    Default(Term),
    /// The initial access to each address must have [Access::create] set to `true`.
    OnlyInit,
}

/// A RAM transcript
#[derive(Debug)]
pub struct Ram {
    /// BoundaryConditions
    boundary_conditions: BoundaryConditions,
    /// The unique id of this RAM
    id: usize,
    /// The sort for times, indices, and values.
    sort: Sort,
    /// The size
    size: usize,
    /// The list of accesses (in access order)
    accesses: VecDeque<Access>,
    /// The maximum time
    next_time: usize,
    /// Whether we're no longer increasing time.
    end_of_time: bool,
    /// The configuration of this RAM
    cfg: AccessCfg,
}

impl Ram {
    fn new(
        id: usize,
        size: usize,
        cfg: AccessCfg,
        boundary_conditions: BoundaryConditions,
    ) -> Self {
        assert!(!matches!(
            &boundary_conditions,
            BoundaryConditions::OnlyInit
        ));
        Ram {
            boundary_conditions,
            id,
            sort: Sort::Field(cfg.field.clone()),
            cfg,
            accesses: Default::default(),
            size,
            next_time: 1,
            end_of_time: false,
        }
    }
    #[track_caller]
    #[allow(unused_variables)]
    fn assert_field(&self, other: &Term) {
        #[cfg(debug_assertions)]
        {
            let s = check(other);
            if let Sort::Field(f) = s {
                if f != self.cfg.field {
                    panic!("RAM field {} is not term field {}", self.cfg.field, f);
                }
            } else {
                panic!("RAM field {} is not term sort {}", self.cfg.field, s);
            }
        }
    }
    fn next_time_term(&mut self) -> Term {
        let t = self.sort.nth_elem(self.next_time);
        if !self.end_of_time {
            self.next_time += 1;
        }
        t
    }
    fn new_read(&mut self, idx: Term, computation: &mut Computation, read_value: Term) -> Term {
        let val_name = format!("__ram{}_read_v{}", self.id, self.accesses.len());
        self.assert_field(&idx);
        self.assert_field(&read_value);
        debug_assert!(!self.end_of_time);

        let var = computation.new_var(
            &val_name,
            self.sort.clone(),
            Some(crate::ir::proof::PROVER_ID),
            Some(read_value),
        );
        let time = self.next_time_term();
        trace!("read: ops: idx {}, time {}", idx.op(), time.op());
        self.accesses
            .push_back(Access::new_read(&self.cfg, idx, var.clone(), time));
        var
    }
    fn new_final_read(&mut self, idx: Term, val: Term) {
        self.assert_field(&idx);
        self.assert_field(&val);
        self.end_of_time = true;
        let time = self.next_time_term();
        trace!(
            "final read: ops: idx {}, val {}, time {}",
            idx.op(),
            val.op(),
            time.op()
        );
        self.accesses
            .push_back(Access::new_read(&self.cfg, idx, val, time))
    }
    fn new_write(&mut self, idx: Term, val: Term, guard: Term) {
        debug_assert!(!self.end_of_time);
        self.assert_field(&idx);
        self.assert_field(&val);
        debug_assert_eq!(&check(&guard), &Sort::Bool);
        let time = self.next_time_term();
        trace!(
            "write: ops: idx {}, val {}, guard {}, time {}",
            idx.op(),
            val.op(),
            guard.op(),
            time.op()
        );
        self.accesses
            .push_back(Access::new_write(&self.cfg, idx, val, guard, time));
    }
    fn new_init(&mut self, idx: Term, val: Term) {
        self.assert_field(&idx);
        self.assert_field(&val);
        self.end_of_time = true;
        trace!("init: ops: idx {}, val {}", idx.op(), val.op());
        self.accesses
            .push_front(Access::new_init(&self.cfg, idx, val));
    }
}
