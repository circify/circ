//! Machinery for formatting IR types
use super::{
    ext, Array, ComputationMetadata, Node, Op, PartyId, PostOrderIter, Sort, Term, TermMap, Value,
    VariableMetadata,
};
use crate::cfg::{cfg, is_cfg_set};

use circ_fields::{FieldT, FieldV};

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use itertools::Itertools;

use std::fmt::{Debug, Display, Error as FmtError, Formatter, Result as FmtResult, Write};

/// State that influences how IR is formatted.
struct IrFormatter<'a, 'b> {
    cfg: &'a IrCfg,
    default_field: Option<FieldT>,
    defs: Defs,
    writer: &'a mut Formatter<'b>,
}

/// IR formatting configuration.
pub struct IrCfg {
    /// Whether to introduce a default modulus.
    pub use_default_field: bool,
    /// Whether to show any moduli
    pub hide_field: bool,
}

impl IrCfg {
    /// Create, from CirC's global configuration
    ///
    /// If the global configuration is not available, uses [IrCfg::parseable].
    pub fn from_circ_cfg() -> Self {
        if is_cfg_set() {
            Self {
                use_default_field: cfg().fmt.use_default_field,
                hide_field: cfg().fmt.hide_field,
            }
        } else {
            Self::parseable()
        }
    }
    /// Create, with values that ensure parseability.
    pub fn parseable() -> Self {
        Self {
            use_default_field: true,
            hide_field: false,
        }
    }
}

/// A wrapper around an IR formattable type, with a configuration.
/// Implements [Display] and [Debug] for various IR types.
pub struct IrWrapper<'a, T> {
    t: &'a T,
    cfg: IrCfg,
}

/// Wrap a reference for IR formatting. Uses [IrCfg::from_circ_cfg].
pub fn wrap<T>(t: &T) -> IrWrapper<T> {
    IrWrapper::new(t, IrCfg::from_circ_cfg())
}

impl<'a, T> IrWrapper<'a, T> {
    /// Create
    pub fn new(t: &'a T, cfg: IrCfg) -> Self {
        Self { t, cfg }
    }
    /// Builder function. Sets [IrCfg::use_default_field].
    pub fn use_default_field(mut self, use_default_field: bool) -> Self {
        self.cfg.use_default_field = use_default_field;
        self
    }
}

#[derive(Default)]
struct Defs {
    terms: TermMap<usize>,
    //    values: HashMap<Value, usize>,
    //    integers: HashMap<Integer, usize>,
    //    sorts: HashMap<Sort, usize>,
    next_id: usize,
}

impl<'a, 'b> IrFormatter<'a, 'b> {
    fn new(writer: &'a mut Formatter<'b>, cfg: &'a IrCfg) -> Self {
        Self {
            cfg,
            default_field: None,
            defs: Default::default(),
            writer,
        }
    }
    fn write_def(&mut self, id: usize) -> FmtResult {
        write!(self.writer, "'{id}")
    }
    /// returns whether the term was def'd and written.
    fn term_write_if_def(&mut self, t: &Term) -> Result<bool, FmtError> {
        if let Some(d) = self.defs.terms.get(t) {
            self.write_def(*d).map(|_| true)
        } else {
            Ok(false)
        }
    }
    /// def a new term
    fn term_def(&mut self, t: Term) -> usize {
        self.defs.next_id += 1;
        assert!(self.defs.terms.insert(t, self.defs.next_id - 1).is_none());
        self.defs.next_id - 1
    }
}

impl<'a, 'b> Write for IrFormatter<'a, 'b> {
    fn write_str(&mut self, s: &str) -> FmtResult {
        self.writer.write_str(s)
    }
}

trait DisplayIr {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult;
}

impl DisplayIr for Sort {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::BitVector(n) => write!(f, "(bv {n})"),
            Sort::Int => write!(f, "int"),
            Sort::F32 => write!(f, "f32"),
            Sort::F64 => write!(f, "f64"),
            Sort::Field(fty) => write!(f, "(mod {})", fty.modulus()),
            Sort::Array(k, v, n) => {
                // we could make our own write macro.
                write!(f, "(array ")?;
                k.ir_fmt(f)?;
                write!(f, " ")?;
                v.ir_fmt(f)?;
                write!(f, " {n})")
            }
            Sort::Tuple(fields) => {
                write!(f, "(tuple")?;
                for field in fields.iter() {
                    write!(f, " ")?;
                    field.ir_fmt(f)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl DisplayIr for Op {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        match self {
            Op::Ite => write!(f, "ite"),
            Op::Eq => write!(f, "="),
            Op::Var(n, _) => write!(f, "{n}"),
            Op::Const(c) => c.ir_fmt(f),
            Op::BvBinOp(a) => write!(f, "{a}"),
            Op::BvBinPred(a) => write!(f, "{a}"),
            Op::BvNaryOp(a) => write!(f, "{a}"),
            Op::BvUnOp(a) => write!(f, "{a}"),
            Op::BoolToBv => write!(f, "bool2bv"),
            Op::BvExtract(a, b) => write!(f, "(extract {a} {b})"),
            Op::BvConcat => write!(f, "concat"),
            Op::BvUext(a) => write!(f, "(uext {a})"),
            Op::BvSext(a) => write!(f, "(sext {a})"),
            Op::PfToBv(a) => write!(f, "(pf2bv {a})"),
            Op::Implies => write!(f, "=>"),
            Op::BoolNaryOp(a) => write!(f, "{a}"),
            Op::Not => write!(f, "not"),
            Op::BvBit(a) => write!(f, "(bit {a})"),
            Op::BoolMaj => write!(f, "maj"),
            Op::FpBinOp(a) => write!(f, "{a}"),
            Op::FpBinPred(a) => write!(f, "{a}"),
            Op::FpUnPred(a) => write!(f, "{a}"),
            Op::FpUnOp(a) => write!(f, "{a}"),
            Op::BvToFp => write!(f, "bv2fp"),
            Op::UbvToFp(a) => write!(f, "(ubv2fp {a})"),
            Op::SbvToFp(a) => write!(f, "(sbv2fp {a})"),
            Op::FpToFp(a) => write!(f, "(fp2fp {a})"),
            Op::PfUnOp(a) => write!(f, "{a}"),
            Op::PfNaryOp(a) => write!(f, "{a}"),
            Op::PfDiv => write!(f, "/"),
            Op::IntNaryOp(a) => write!(f, "{a}"),
            Op::IntBinPred(a) => write!(f, "{a}"),
            Op::UbvToPf(a) => write!(f, "(bv2pf {})", a.modulus()),
            Op::PfChallenge(n, m) => write!(f, "(challenge {} {})", n, m.modulus()),
            Op::PfFitsInBits(n) => write!(f, "(pf_fits_in_bits {})", n),
            Op::Select => write!(f, "select"),
            Op::Store => write!(f, "store"),
            Op::CStore => write!(f, "cstore"),
            Op::Fill(key_sort, size) => {
                write!(f, "(fill ")?;
                key_sort.ir_fmt(f)?;
                write!(f, " {})", *size)
            }
            Op::Array(k, v) => {
                write!(f, "(array ")?;
                k.ir_fmt(f)?;
                write!(f, " ")?;
                v.ir_fmt(f)?;
                write!(f, ")")
            }
            Op::Tuple => write!(f, "tuple"),
            Op::Field(i) => write!(f, "(field {i})"),
            Op::Update(i) => write!(f, "(update {i})"),
            Op::Map(op) => {
                write!(f, "(map(")?;
                op.ir_fmt(f)?;
                write!(f, "))")
            }
            Op::Call(name, a, r) => {
                let arg_sorts = a.iter().map(|x| x.to_string()).join(" ");
                write!(f, "(call {name} ({arg_sorts}) {r})")
            }
            Op::Rot(i) => write!(f, "(rot {i})"),
            Op::PfToBoolTrusted => write!(f, "pf2bool_trusted"),
            Op::ExtOp(o) => o.ir_fmt(f),
        }
    }
}

impl DisplayIr for ext::ExtOp {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        match self {
            ext::ExtOp::Haboeck => write!(f, "haboeck"),
            ext::ExtOp::PersistentRamSplit => write!(f, "persistent_ram_split"),
            ext::ExtOp::UniqDeriGcd => write!(f, "uniq_deri_gcd"),
            ext::ExtOp::Sort => write!(f, "sort"),
            ext::ExtOp::Waksman => write!(f, "Waksman"),
        }
    }
}

impl DisplayIr for Value {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::F32(b) => write!(f, "{b}"),
            Value::F64(b) => write!(f, "{b}"),
            Value::Int(b) => write!(f, "{b}"),
            Value::Field(b) => b.ir_fmt(f),
            Value::BitVector(b) => write!(f, "{b}"),
            Value::Tuple(fields) => {
                write!(f, "(#t")?;
                for field in fields.iter() {
                    write!(f, " ")?;
                    field.ir_fmt(f)?;
                }
                write!(f, ")")
            }
            Value::Array(a) => a.ir_fmt(f),
        }
    }
}

impl DisplayIr for Array {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        if self.map.len() == self.size && *self.default == self.default.sort().default_value() {
            write!(f, "(#l ")?;
            self.key_sort.ir_fmt(f)?;
            write!(f, " (")?;
            let mut first = true;
            for ((k, v), expected_k) in self.map.iter().zip(self.key_sort.elems_iter_values()) {
                assert_eq!(k, &expected_k, "Expected key {expected_k}, got {k}");
                if !first {
                    write!(f, " ")?;
                }
                v.ir_fmt(f)?;
                first = false;
            }
            write!(f, "))")
        } else {
            write!(f, "(#a ")?;
            self.key_sort.ir_fmt(f)?;
            write!(f, " ")?;
            self.default.ir_fmt(f)?;
            write!(f, " {} (", self.size)?;
            let mut first = true;
            for (k, v) in &self.map {
                if !first {
                    write!(f, " ")?;
                }
                write!(f, "(")?;
                k.ir_fmt(f)?;
                write!(f, " ")?;
                v.ir_fmt(f)?;
                write!(f, ")")?;
                first = false;
            }
            write!(f, "))")
        }
    }
}

impl DisplayIr for FieldV {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        let omit_field = f.cfg.hide_field
            || f.default_field
                .as_ref()
                .map_or(false, |field| field == &self.ty());
        let mut i = self.i();
        let mod_bits = self.modulus().significant_bits();
        if i.significant_bits() + 1 >= mod_bits {
            i -= self.modulus();
        }
        write!(f, "#f{i}")?;
        if !omit_field {
            write!(f, "m{}", self.modulus())?;
        }
        Ok(())
    }
}

impl DisplayIr for Term {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        let written = f.term_write_if_def(self)?;
        if !written {
            let use_parenthesis = match self.op().arity() {
                Some(0) => false,
                Some(_) => true,
                None => true,
            };
            if use_parenthesis {
                write!(f, "(")?;
            }
            self.op().ir_fmt(f)?;
            for c in self.cs() {
                write!(f, " ")?;
                c.ir_fmt(f)?;
            }
            if use_parenthesis {
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

impl DisplayIr for VariableMetadata {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        write!(f, "({} ", self.name)?;
        self.sort.ir_fmt(f)?;
        if let Some(v) = self.vis.as_ref() {
            write!(f, " (party {v})")?;
        }
        if 0 != self.round {
            write!(f, " (round {})", self.round)?;
        }
        if self.random {
            write!(f, " (random)")?;
        }
        if self.committed {
            write!(f, " (committed)")?;
        }
        write!(f, ")")
    }
}

impl DisplayIr for ComputationMetadata {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        write!(f, "(metadata\n  (parties ")?;
        let ids_to_parties: HashMap<PartyId, &str> = self
            .party_ids
            .iter()
            .map(|(name, id)| (*id, name.as_str()))
            .collect();
        for id in 0..self.party_ids.len() as u8 {
            let party = ids_to_parties.get(&id).unwrap();
            write!(f, " {party}")?;
        }
        writeln!(f, ")")?;
        write!(f, "\n  (inputs")?;
        for v in self.vars.values() {
            write!(f, "\n    ")?;
            v.ir_fmt(f)?;
        }
        write!(f, "\n  )")?;
        write!(f, "\n  (commitments")?;
        for c in &self.commitments {
            write!(f, "\n    (commitment")?;
            for n in c {
                write!(f, " {n}")?;
            }
            write!(f, ")")?;
        }
        write!(f, "\n  )")?;
        write!(f, "\n)")
    }
}

/// Format a term, introducing bindings.
fn fmt_term_with_bindings(t: &Term, f: &mut IrFormatter) -> FmtResult {
    let close_dft_f = if f.cfg.use_default_field && f.default_field.is_none() {
        let fields: HashSet<FieldT> = PostOrderIter::new(t.clone())
            .filter_map(|c| {
                if let Op::Const(Value::Field(f)) = &c.op() {
                    Some(f.ty())
                } else {
                    None
                }
            })
            .collect();
        if fields.len() == 1 && !f.cfg.hide_field {
            f.default_field = fields.into_iter().next();
            let i = f.default_field.clone().unwrap();
            writeln!(f, "(set_default_modulus {}", i.modulus())?;
            true
        } else {
            false
        }
    } else {
        false
    };

    let mut n_bindings = 0;
    let mut parent_counts = TermMap::<usize>::default();
    writeln!(f, "(declare")?;
    writeln!(f, " (")?;
    for t in PostOrderIter::new(t.clone()) {
        for c in t.cs().iter().cloned() {
            let has_children = !c.cs().is_empty();
            let count = parent_counts.entry(c).or_insert(0);
            *count += 1;
            if *count == 2 && has_children {
                n_bindings += 1;
            }
        }
        if let Op::Var(name, sort) = &t.op() {
            write!(f, "  ({name} ")?;
            sort.ir_fmt(f)?;
            writeln!(f, ")")?;
        }
    }
    writeln!(f, " )")?;
    if n_bindings > 0 {
        writeln!(f, " (let")?;
        writeln!(f, "  (")?; // let binding list
        for t in PostOrderIter::new(t.clone()) {
            if parent_counts.get(&t).unwrap_or(&0) > &1 && !t.cs().is_empty() {
                write!(f, "   ('{} ", f.defs.next_id.clone(),)?;
                t.ir_fmt(f)?;
                writeln!(f, ")")?;
                f.term_def(t);
            }
        }
        writeln!(f, "  )")?; // let binding list
        writeln!(f, "  ")?;
        t.ir_fmt(f)?;
        writeln!(f, ")")?; // let
    } else {
        t.ir_fmt(f)?;
    }
    writeln!(f, ")")?; // declare
    if close_dft_f {
        writeln!(f, ")")?;
    }
    Ok(())
}

impl<'a> Display for IrWrapper<'a, Term> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{self:?}")
    }
}

impl<'a> Debug for IrWrapper<'a, Term> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let cfg = IrCfg::from_circ_cfg();
        let f = &mut IrFormatter::new(f, &cfg);
        fmt_term_with_bindings(self.t, f)
    }
}

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let cfg = IrCfg::from_circ_cfg();
        let f = &mut IrFormatter::new(f, &cfg);
        if let Op::Const(c) = self.op() {
            c.ir_fmt(f)
        } else {
            fmt_term_with_bindings(self, f)
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{self:?}")
    }
}

macro_rules! fmt_impl {
    ($trait:ty, $ty:ty) => {
        impl $trait for $ty {
            fn fmt(&self, f: &mut Formatter) -> FmtResult {
                self.ir_fmt(&mut IrFormatter::new(f, &IrCfg::from_circ_cfg()))
            }
        }
    };
}

fmt_impl!(Display, Sort);
fmt_impl!(Display, Value);
fmt_impl!(Display, Op);
fmt_impl!(Display, ComputationMetadata);
fmt_impl!(Debug, Value);
fmt_impl!(Debug, Sort);
fmt_impl!(Debug, Op);
