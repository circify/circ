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
    /// A (field) hash of the value read or (conditionally) written.
    pub val_hash: Option<Term>,
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
    waksman: bool,
    covering_rom: bool,
    haboeck: bool,
}

impl AccessCfg {
    /// Create a new configuration
    pub fn new(field: FieldT, opt: RamOpt, create: bool) -> Self {
        use circ_opt::{IndexStrategy, PermutationStrategy, RangeStrategy, RomStrategy};
        Self {
            false_: bool_lit(false),
            true_: bool_lit(true),
            one: pf_lit(field.new_v(1)),
            zero: pf_lit(field.new_v(0)),
            field,
            create,
            sort_indices: opt.index == IndexStrategy::Sort,
            split_times: opt.range == RangeStrategy::BitSplit,
            waksman: opt.permutation == PermutationStrategy::Waksman,
            covering_rom: false,
            haboeck: opt.rom == RomStrategy::Haboeck,
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
            waksman: false,
            covering_rom: false,
            haboeck: true,
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
    fn val_sort_len(s: &Sort) -> usize {
        match s {
            Sort::Tuple(t) => t.iter().map(Self::val_sort_len).sum(),
            Sort::Array(_, v, size) => *size * Self::val_sort_len(v),
            _ => 1,
        }
    }
    fn len(&self, s: &Sort) -> usize {
        (if self.covering_rom {
            1
        } else if self.create {
            5
        } else {
            4
        }) + Self::val_sort_len(s)
    }
    fn bool2pf(&self, t: Term) -> Term {
        term![Op::Ite; t, self.one.clone(), self.zero.clone()]
    }
    fn pf_neg(&self, t: Term) -> Term {
        term![PF_ADD; self.one.clone(), term![PF_NEG; t]]
    }
    fn pf_lit(&self, i: usize) -> Term {
        pf_lit(self.field.new_v(i))
    }
}

fn scalar_to_field(scalar: &Term, c: &AccessCfg) -> Term {
    match check(scalar) {
        Sort::Field(f) => {
            if f == c.field {
                scalar.clone()
            } else {
                panic!("Cannot convert scalar of field {} to field {}", f, c.field)
            }
        }
        Sort::Bool => c.bool2pf(scalar.clone()),
        Sort::BitVector(_) => term![Op::UbvToPf(c.field.clone()); scalar.clone()],
        s => panic!("non-scalar sort {}", s),
    }
}

/// A bit encoded in the field.
#[derive(Debug, Clone)]
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
            val_hash: None,
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
            val_hash: None,
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
            val_hash: None,
            idx,
            time: f.zero.clone(),
            write: FieldBit::from_bool_lit(f, true),
            active: FieldBit::from_bool_lit(f, true),
            create: FieldBit::from_bool_lit(f, true),
        }
    }

    fn field_names(c: &AccessCfg, sort: &Sort, order: Order) -> Vec<String> {
        let mut out = Vec::new();
        let metadata = !c.covering_rom;
        match order {
            Order::Hash => {
                Self::sort_subnames(sort, "v", &mut out);
                out.push("i".into());
                if metadata {
                    out.push("t".into());
                    out.push("w".into());
                    out.push("a".into());
                    if c.create {
                        out.push("c".into());
                    }
                }
            }
            // dead code, but for clarity...
            Order::Sort => {
                out.push("i".into());
                if metadata {
                    out.push("t".into());
                    if c.create {
                        out.push("c".into());
                    }
                }
                Self::sort_subnames(sort, "v", &mut out);
                if metadata {
                    out.push("w".into());
                    out.push("a".into());
                }
            }
        }
        out
    }

    fn sort_subnames(sort: &Sort, prefix: &str, out: &mut Vec<String>) {
        match sort {
            Sort::Field(_) | Sort::Bool | Sort::BitVector(_) => out.push(prefix.into()),
            Sort::Tuple(ss) => {
                for (i, s) in ss.iter().enumerate() {
                    Self::sort_subnames(s, &format!("{}_{}", prefix, i), out);
                }
            }
            Sort::Array(_, v, size) => {
                for i in 0..*size {
                    Self::sort_subnames(v, &format!("{}_{}", prefix, i), out);
                }
            }
            _ => unreachable!(),
        }
    }

    /// Serialize a value as field elements.
    fn val_to_field_elements(val: &Term, c: &AccessCfg, out: &mut Vec<Term>) {
        match check(val) {
            Sort::Field(_) | Sort::Bool | Sort::BitVector(_) => out.push(scalar_to_field(val, c)),
            Sort::Tuple(ss) => {
                for i in 0..ss.len() {
                    Self::val_to_field_elements(&term![Op::Field(i); val.clone()], c, out);
                }
            }
            Sort::Array(_, _, size) => {
                for i in 0..size {
                    Self::val_to_field_elements(
                        &term![Op::Select; val.clone(), c.pf_lit(i)],
                        c,
                        out,
                    );
                }
            }
            _ => unreachable!(),
        }
    }

    fn val_from_field_elements_trusted(sort: &Sort, next: &mut impl FnMut() -> Term) -> Term {
        match sort {
            Sort::Field(_) => next().clone(),
            Sort::Bool => term![Op::PfToBoolTrusted; next().clone()],
            Sort::BitVector(w) => term![Op::PfToBv(*w); next().clone()],
            Sort::Tuple(ss) => term(
                Op::Tuple,
                ss.iter()
                    .map(|s| Self::val_from_field_elements_trusted(s, next))
                    .collect(),
            ),
            Sort::Array(k, v, size) => term(
                Op::Array(*k.clone(), *v.clone()),
                (0..*size)
                    .map(|_| Self::val_from_field_elements_trusted(v, next))
                    .collect(),
            ),
            _ => unreachable!(),
        }
    }

    /// Encode this access as a sequence of field terms.
    ///
    /// The sequence depends on `order` and on `c`.
    ///
    /// For example, if `c.covering_rom` is set, then the sequence will only contain an encoding of
    /// the indices and values.
    fn to_field_elems(&self, c: &AccessCfg, order: Order) -> Vec<Term> {
        let mut out = Vec::new();
        let metadata = !c.covering_rom;
        match order {
            Order::Hash => {
                Self::val_to_field_elements(&self.val, c, &mut out);
                out.push(self.idx.clone());
                if metadata {
                    out.push(self.time.clone());
                    out.push(self.write.f.clone());
                    out.push(self.active.f.clone());
                    if c.create {
                        out.push(self.create.f.clone())
                    }
                }
            }
            Order::Sort => {
                out.push(self.idx.clone());
                if metadata {
                    out.push(self.time.clone());
                    if c.create {
                        out.push(self.create.f.clone())
                    }
                }
                Self::val_to_field_elements(&self.val, c, &mut out);
                if metadata {
                    out.push(self.write.f.clone());
                    out.push(self.active.f.clone());
                }
            }
        }
        out
    }

    /// Decode this access as a sequence of field terms, assuming that those field terms are the
    /// encoding of an access.
    ///
    /// The expected order of field terms depends on `c` and `order`; see [Access::to_field_elems].
    fn from_field_elems_trusted(
        elems: Vec<Term>,
        val_sort: &Sort,
        c: &AccessCfg,
        order: Order,
    ) -> Self {
        debug_assert_eq!(elems.len(), c.len(val_sort));
        let mut elems = elems.into_iter();
        let mut next = || {
            let t = elems.next().unwrap();
            debug_assert!(matches!(check(&t), Sort::Field(_)));
            t
        };
        let metadata = !c.covering_rom;
        let f = FieldBit::from_bool_lit(c, false);
        match order {
            Order::Hash => Self {
                val: Self::val_from_field_elements_trusted(val_sort, &mut next),
                val_hash: None,
                idx: next(),
                time: if metadata { next() } else { c.pf_lit(0) },
                write: if metadata {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    f.clone()
                },
                active: if metadata {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    f.clone()
                },
                create: if c.create && metadata {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    FieldBit::from_bool_lit(c, false)
                },
            },
            Order::Sort => Self {
                val_hash: None,
                idx: next(),
                time: if metadata { next() } else { c.pf_lit(0) },
                create: if c.create && metadata {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    FieldBit::from_bool_lit(c, false)
                },
                val: Self::val_from_field_elements_trusted(val_sort, &mut next),
                write: if metadata {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    f.clone()
                },
                active: if metadata {
                    FieldBit::from_trusted_field(c, next())
                } else {
                    f.clone()
                },
            },
        }
    }

    fn universal_hash(
        &self,
        c: &AccessCfg,
        val_sort: &Sort,
        hasher: &hash::UniversalHasher,
    ) -> (Term, Term) {
        assert_eq!(hasher.len(), c.len(val_sort));
        let mut val_elems = Vec::new();
        Self::val_to_field_elements(&self.val, c, &mut val_elems);
        (
            hasher.hash(self.to_field_elems(c, Order::Hash)),
            hasher.hash(val_elems),
        )
    }

    fn to_field_tuple(&self, c: &AccessCfg) -> Term {
        term(Op::Tuple, self.to_field_elems(c, Order::Sort))
    }

    fn declare_trusted(
        c: &AccessCfg,
        mut declare_var: impl FnMut(&str, Term) -> Term,
        val_sort: &Sort,
        value_tuple: Term,
    ) -> Self {
        let mut declare_field =
            |name: &str, idx: usize| declare_var(name, term![Op::Field(idx); value_tuple.clone()]);
        let elems = Self::field_names(c, val_sort, Order::Sort)
            .iter()
            .enumerate()
            .map(|(idx, name)| declare_field(name, idx))
            .collect();
        Self::from_field_elems_trusted(elems, val_sort, c, Order::Sort)
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
    /// The sort for times and indices.
    sort: Sort,
    /// The sort for values.
    val_sort: Sort,
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

#[allow(dead_code)]
/// Are terms of sort `s` hashable using a UHF keyed by field type `f`.
fn hashable(s: &Sort, f: &FieldT) -> bool {
    match s {
        Sort::Field(ff) => f == ff,
        Sort::Tuple(ss) => ss.iter().all(|s| hashable(s, f)),
        Sort::BitVector(_) => true,
        Sort::Bool => true,
        Sort::Array(_k, v, size) => *size < 20 && hashable(v, f),
        _ => false,
    }
}

impl Ram {
    fn new(
        id: usize,
        size: usize,
        cfg: AccessCfg,
        val_sort: Sort,
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
            val_sort,
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
    #[track_caller]
    #[allow(unused_variables)]
    /// Assert that `other` is hashable using the field of `self`.
    fn assert_hashable(&self, other: &Term) {
        #[cfg(debug_assertions)]
        {
            let s = check(other);
            if !hashable(&s, &self.cfg.field) {
                panic!(
                    "RAM field of sort {} is not hashable with field {}",
                    s, self.cfg.field
                );
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
        self.assert_hashable(&read_value);
        debug_assert!(!self.end_of_time);

        let var = computation.new_var(
            &val_name,
            self.val_sort.clone(),
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
        self.assert_hashable(&val);
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
        self.assert_hashable(&val);
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
        self.assert_hashable(&val);
        self.end_of_time = true;
        trace!("init: ops: idx {}, val {}", idx.op(), val.op());
        self.accesses
            .push_front(Access::new_init(&self.cfg, idx, val));
    }
    /// A ROM is a RAM in which there is only one write to any location, and that write happens
    /// *before* any read.
    ///
    /// A covering ROM is a ROM with a write to every location.
    ///
    /// This function computes whether the first accesses are writes to distinct locations, and
    /// whether the rest are reads.
    fn is_covering_rom(&self) -> bool {
        let mut written_addresses = TermSet::default();
        for access in self.accesses.iter().take(self.size) {
            if !access.idx.is_const()
                || access.write.b != bool_lit(true)
                || access.active.b != bool_lit(true)
            {
                trace!(
                    "non-ROM because of an early non-const or non-read to {}",
                    access.idx
                );
                return false;
            }
            if !written_addresses.insert(access.idx.clone()) {
                trace!("non-ROM because of a 2nd access to {}", access.idx);
                return false;
            }
        }
        for access in self.accesses.iter().skip(self.size) {
            if access.write.b != bool_lit(false) && access.active.b != bool_lit(false) {
                trace!("non-ROM because of a late write to {}", access.idx);
                return false;
            }
        }
        true
    }
}
