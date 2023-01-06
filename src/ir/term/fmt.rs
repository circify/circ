//! Machinery for formatting IR types
use super::{mk_ref, Array, Op, PostOrderIter, Sort, Term, TermData, TermMap, Value};
use crate::cfg::{cfg, is_cfg_set};

use circ_fields::{FieldT, FieldV};

use fxhash::FxHashSet as HashSet;

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
}

impl IrCfg {
    /// Create, from CirC's global configuration
    ///
    /// If the global configuration is not available, uses [IrCfg::parseable].
    pub fn from_circ_cfg() -> Self {
        if is_cfg_set() {
            Self {
                use_default_field: cfg().fmt.use_default_field,
            }
        } else {
            Self::parseable()
        }
    }
    /// Create, with values that ensure parseability.
    pub fn parseable() -> Self {
        Self {
            use_default_field: true,
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
        write!(self.writer, "'{}", id)
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
            Sort::BitVector(n) => write!(f, "(bv {})", n),
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
                write!(f, " {})", n)
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
            Op::Var(n, _) => write!(f, "{}", n),
            Op::Const(c) => c.ir_fmt(f),
            Op::BvBinOp(a) => write!(f, "{}", a),
            Op::BvBinPred(a) => write!(f, "{}", a),
            Op::BvNaryOp(a) => write!(f, "{}", a),
            Op::BvUnOp(a) => write!(f, "{}", a),
            Op::BoolToBv => write!(f, "bool2bv"),
            Op::BvExtract(a, b) => write!(f, "(extract {} {})", a, b),
            Op::BvConcat => write!(f, "concat"),
            Op::BvUext(a) => write!(f, "(uext {})", a),
            Op::BvSext(a) => write!(f, "(sext {})", a),
            Op::PfToBv(a) => write!(f, "(pf2bv {})", a),
            Op::Implies => write!(f, "=>"),
            Op::BoolNaryOp(a) => write!(f, "{}", a),
            Op::Not => write!(f, "not"),
            Op::BvBit(a) => write!(f, "(bit {})", a),
            Op::BoolMaj => write!(f, "maj"),
            Op::FpBinOp(a) => write!(f, "{}", a),
            Op::FpBinPred(a) => write!(f, "{}", a),
            Op::FpUnPred(a) => write!(f, "{}", a),
            Op::FpUnOp(a) => write!(f, "{}", a),
            Op::BvToFp => write!(f, "bv2fp"),
            Op::UbvToFp(a) => write!(f, "(ubv2fp {})", a),
            Op::SbvToFp(a) => write!(f, "(sbv2fp {})", a),
            Op::FpToFp(a) => write!(f, "(fp2fp {})", a),
            Op::PfUnOp(a) => write!(f, "{}", a),
            Op::PfNaryOp(a) => write!(f, "{}", a),
            Op::IntNaryOp(a) => write!(f, "{}", a),
            Op::IntBinPred(a) => write!(f, "{}", a),
            Op::UbvToPf(a) => write!(f, "(bv2pf {})", a.modulus()),
            Op::Select => write!(f, "select"),
            Op::Store => write!(f, "store"),
            Op::Tuple => write!(f, "tuple"),
            Op::Field(i) => write!(f, "(field {})", i),
            Op::Update(i) => write!(f, "(update {})", i),
            Op::Map(op) => {
                write!(f, "(map(")?;
                op.ir_fmt(f)?;
                write!(f, "))")
            }
            Op::Call(name, _, _) => write!(f, "fn:{}", name),
            Op::Rot(i) => write!(f, "(rot {})", i),
        }
    }
}

impl DisplayIr for Value {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::F32(b) => write!(f, "{}", b),
            Value::F64(b) => write!(f, "{}", b),
            Value::Int(b) => write!(f, "{}", b),
            Value::Field(b) => b.ir_fmt(f),
            Value::BitVector(b) => write!(f, "{}", b),
            Value::Tuple(fields) => {
                write!(f, "(#t ")?;
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
        write!(f, "(#a ")?;
        self.key_sort.ir_fmt(f)?;
        write!(f, " ")?;
        self.default.ir_fmt(f)?;
        write!(f, " {} (", self.size)?;
        let mut first = true;
        for (k, v) in &self.map {
            if first {
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

impl DisplayIr for FieldV {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        let omit_field = f
            .default_field
            .as_ref()
            .map_or(false, |field| field == &self.ty());
        let mut i = self.i();
        let mod_bits = self.modulus().significant_bits();
        if i.significant_bits() + 1 >= mod_bits {
            i -= self.modulus();
        }
        write!(f, "#f{}", i)?;
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
            <TermData as DisplayIr>::ir_fmt(self, f)?;
        }
        Ok(())
    }
}

impl DisplayIr for TermData {
    fn ir_fmt(&self, f: &mut IrFormatter) -> FmtResult {
        if !self.cs.is_empty() {
            write!(f, "(")?;
        }
        self.op.ir_fmt(f)?;
        for c in &self.cs {
            write!(f, " ")?;
            c.ir_fmt(f)?;
        }
        if !self.cs.is_empty() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

/// Format a term, introducing bindings.
fn fmt_term_with_bindings(t: &Term, f: &mut IrFormatter) -> FmtResult {
    let close_dft_f = if f.cfg.use_default_field && f.default_field.is_none() {
        let fields: HashSet<FieldT> = PostOrderIter::new(t.clone())
            .filter_map(|c| {
                if let Op::Const(Value::Field(f)) = &c.op {
                    Some(f.ty())
                } else {
                    None
                }
            })
            .collect();
        if fields.len() == 1 {
            f.default_field = fields.into_iter().next();
            let i = f.default_field.clone().unwrap();
            writeln!(f, "(set-default-modulus {}", i.modulus())?;
            true
        } else {
            false
        }
    } else {
        false
    };

    let mut parent_counts = TermMap::<usize>::new();
    writeln!(f, "(declare")?;
    writeln!(f, " (")?;
    for t in PostOrderIter::new(t.clone()) {
        for c in t.cs.iter().cloned() {
            *parent_counts.entry(c).or_insert(0) += 1;
        }
        if let Op::Var(name, sort) = &t.op {
            write!(f, "  ({} ", name)?;
            sort.ir_fmt(f)?;
            writeln!(f, ")")?;
        }
    }
    writeln!(f, " )")?;
    writeln!(f, " (let")?;
    writeln!(f, "  (")?;
    for t in PostOrderIter::new(t.clone()) {
        if parent_counts.get(&t).unwrap_or(&0) > &1 && !t.cs.is_empty() {
            write!(f, "   ('{} ", f.defs.next_id.clone(),)?;
            t.ir_fmt(f)?;
            writeln!(f, ")")?;
            f.term_def(t);
        }
    }
    writeln!(f, "  )")?;
    writeln!(f, "  ")?;
    t.ir_fmt(f)?;
    writeln!(f, ")")?;
    writeln!(f, ")")?;
    if close_dft_f {
        writeln!(f, ")")?;
    }
    Ok(())
}

impl<'a> Display for IrWrapper<'a, Term> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl<'a> Debug for IrWrapper<'a, Term> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let cfg = IrCfg::from_circ_cfg();
        let f = &mut IrFormatter::new(f, &cfg);
        fmt_term_with_bindings(self.t, f)
    }
}

impl<'a> Display for IrWrapper<'a, TermData> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl<'a> Debug for IrWrapper<'a, TermData> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let f = &mut IrFormatter::new(f, &self.cfg);
        fmt_term_with_bindings(&mk_ref(self.t), f)
    }
}

impl Debug for TermData {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let cfg = IrCfg::from_circ_cfg();
        let f = &mut IrFormatter::new(f, &cfg);
        fmt_term_with_bindings(&mk_ref(self), f)
    }
}

impl Display for TermData {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.ir_fmt(&mut IrFormatter::new(f, &IrCfg::from_circ_cfg()))
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.ir_fmt(&mut IrFormatter::new(f, &IrCfg::from_circ_cfg()))
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.ir_fmt(&mut IrFormatter::new(f, &IrCfg::from_circ_cfg()))
    }
}
