//! Rank 1 Constraint Systems

use circ_fields::{FieldT, FieldV};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use log::debug;
use paste::paste;
use rug::Integer;
use std::collections::hash_map::Entry;
use std::fmt::Display;
use std::hash::Hash;

#[cfg(feature = "r1cs")]
pub mod bellman;
pub mod opt;
pub mod trans;

#[derive(Clone, Debug)]
/// A Rank 1 Constraint System.
pub struct R1cs<S: Hash + Eq> {
    modulus: FieldT,
    signal_idxs: HashMap<S, usize>,
    idxs_signals: HashMap<usize, S>,
    next_idx: usize,
    public_idxs: HashSet<usize>,
    values: Option<HashMap<usize, FieldV>>,
    constraints: Vec<(Lc, Lc, Lc)>,
}

#[derive(Clone, Debug)]
/// A linear combination
pub struct Lc {
    modulus: FieldT,
    constant: FieldV,
    monomials: HashMap<usize, FieldV>,
}

impl Lc {
    /// Is this the zero combination?
    pub fn is_zero(&self) -> bool {
        self.monomials.is_empty() && self.constant.is_zero()
    }
    /// Make this the zero combination.
    pub fn clear(&mut self) {
        self.monomials.clear();
        self.constant = self.modulus.zero();
    }
    /// Take this linear combination, leaving zero in its place.
    pub fn take(&mut self) -> Self {
        let monomials = std::mem::take(&mut self.monomials);
        let constant = std::mem::replace(&mut self.constant, self.modulus.zero());
        Self {
            modulus: self.modulus.clone(),
            constant,
            monomials,
        }
    }
    /// Is this a constant? If so, return that constant.
    pub fn as_const(&self) -> Option<&FieldV> {
        self.monomials.is_empty().then(|| &self.constant)
    }
}

macro_rules! arith_impl {
    ($Trait: ident, $fn: ident) => {
        paste! {
            impl $Trait<&Lc> for Lc {
                type Output = Self;
                fn $fn(mut self, other: &Self) -> Self {
                    self.[<$fn _assign>](other);
                    self
                }
            }

            impl [<$Trait Assign>]<&Lc> for Lc {
                fn [<$fn _assign>](&mut self, other: &Self) {
                    assert_eq!(&self.modulus, &other.modulus);
                    self.constant.[<$fn _assign>](&other.constant);
                    let tot = self.monomials.len() + other.monomials.len();
                    if tot > self.monomials.capacity() {
                        self.monomials.reserve(tot - self.monomials.capacity());
                    }
                    for (i, v) in &other.monomials {
                        match self.monomials.entry(*i) {
                            Entry::Occupied(mut e) => {
                                e.get_mut().[<$fn _assign>](v);
                                if e.get().is_zero() {
                                    e.remove_entry();
                                }
                            }
                            Entry::Vacant(e) => {
                                let mut m = self.modulus.zero();
                                m.[<$fn _assign>](v);
                                e.insert(m);
                            }
                        }
                    }
                }
            }

            impl $Trait<&FieldV> for Lc {
                type Output = Self;
                fn $fn(mut self, other: &FieldV) -> Self {
                    self.[<$fn _assign>](other);
                    self
                }
            }

            impl [<$Trait Assign>]<&FieldV> for Lc {
                fn [<$fn _assign>](&mut self, other: &FieldV) {
                    self.constant.[<$fn _assign>](other);
                }
            }

            impl [<$Trait Assign>]<FieldV> for Lc {
                fn [<$fn _assign>](&mut self, other: FieldV) {
                    self.[<$fn _assign>](&other);
                }
            }

            impl $Trait<isize> for Lc {
                type Output = Self;
                fn $fn(mut self, other: isize) -> Self {
                    self.[<$fn _assign>](other);
                    self
                }
            }

            impl [<$Trait Assign>]<isize> for Lc {
                fn [<$fn _assign>](&mut self, other: isize) {
                    self.constant.[<$fn _assign>](self.modulus.new_v(other));
                }
            }
        }
    };
}

use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

impl Neg for Lc {
    type Output = Lc;
    fn neg(mut self) -> Lc {
        self.constant = -self.constant;
        for v in &mut self.monomials.values_mut() {
            *v = -v.clone();
        }
        self
    }
}

arith_impl! {Add, add}
arith_impl! {Sub, sub}

impl Mul<&FieldV> for Lc {
    type Output = Lc;
    fn mul(mut self, other: &FieldV) -> Lc {
        self *= other;
        self
    }
}

impl MulAssign<FieldV> for Lc {
    fn mul_assign(&mut self, other: FieldV) {
        self.mul_assign(&other);
    }
}

impl MulAssign<&FieldV> for Lc {
    fn mul_assign(&mut self, other: &FieldV) {
        self.constant *= other;
        if other.is_zero() {
            self.monomials.clear();
        } else {
            for v in &mut self.monomials.values_mut() {
                *v *= other;
            }
        }
    }
}

impl Mul<isize> for Lc {
    type Output = Lc;
    fn mul(mut self, other: isize) -> Lc {
        self *= other;
        self
    }
}

impl MulAssign<isize> for Lc {
    fn mul_assign(&mut self, other: isize) {
        self.mul_assign(self.modulus.new_v(other));
    }
}

impl<S: Clone + Hash + Eq + Display> R1cs<S> {
    /// Make an empty constraint system, mod `modulus`.
    /// If `values`, then this constraint system will track & expect concrete values.
    pub fn new(modulus: FieldT, values: bool) -> Self {
        R1cs {
            modulus,
            signal_idxs: HashMap::default(),
            idxs_signals: HashMap::default(),
            next_idx: 0,
            public_idxs: HashSet::default(),
            values: if values {
                Some(HashMap::default())
            } else {
                None
            },
            constraints: Vec::new(),
        }
    }
    /// Get the zero combination for this system.
    pub fn zero(&self) -> Lc {
        Lc {
            modulus: self.modulus.clone(),
            constant: self.modulus.zero(),
            monomials: HashMap::default(),
        }
    }
    /// Get a constant constraint for this system.
    #[track_caller]
    pub fn constant(&self, c: FieldV) -> Lc {
        assert_eq!(c.ty(), self.modulus);
        Lc {
            modulus: self.modulus.clone(),
            constant: c,
            monomials: HashMap::default(),
        }
    }
    /// Get combination which is just the wire `s`.
    pub fn signal_lc(&self, s: &S) -> Lc {
        let idx = self
            .signal_idxs
            .get(s)
            .expect("Missing signal in signal_lc");
        let mut lc = self.zero();
        lc.monomials.insert(*idx, self.modulus.new_v(1));
        lc
    }
    /// Create a new wire, `s`. If this system is tracking concrete values, you must provide the
    /// value, `v`.
    pub fn add_signal(&mut self, s: S, v: Option<FieldV>) {
        let n = self.next_idx;
        self.next_idx += 1;
        self.signal_idxs.insert(s.clone(), n);
        self.idxs_signals.insert(n, s);
        match (self.values.as_mut(), v) {
            (Some(vs), Some(v)) => {
                //println!("{} -> {}", &s, &v);
                vs.insert(n, v);
            }
            (None, None) => {}
            (Some(_), _) => panic!("R1cs is storing values, but none provided"),
            (_, Some(_)) => panic!("R1cs is not storing values, but one provided"),
        }
    }
    /// Make `s` a public wire in the system
    pub fn publicize(&mut self, s: &S) {
        self.signal_idxs
            .get(s)
            .cloned()
            .map(|i| self.public_idxs.insert(i));
    }
    /// Make `a * b = c` a constraint.
    pub fn constraint(&mut self, a: Lc, b: Lc, c: Lc) {
        assert_eq!(&self.modulus, &a.modulus);
        assert_eq!(&self.modulus, &b.modulus);
        assert_eq!(&self.modulus, &c.modulus);
        debug!(
            "Constraint:\n    {}\n  * {}\n  = {}",
            self.format_lc(&a),
            self.format_lc(&b),
            self.format_lc(&c)
        );
        self.constraints.push((a.clone(), b.clone(), c.clone()));
        if self.values.is_some() {
            self.check(&a, &b, &c);
        }
    }
    /// Get a nice string represenation of the combination `a`.
    pub fn format_lc(&self, a: &Lc) -> String {
        let mut s = String::new();

        let half_m: Integer = self.modulus().clone() / 2;
        let abs = |i: Integer| {
            if i <= half_m {
                i
            } else {
                self.modulus() - i
            }
        };
        let sign = |i: &Integer| if i < &half_m { "+" } else { "-" };
        let format_i = |i: &FieldV| {
            let ii: Integer = i.into();
            format!("{}{}", sign(&ii), abs(ii))
        };

        s.push_str(&format_i(&a.constant));
        for (idx, coeff) in &a.monomials {
            s.extend(
                format!(
                    " {} {}",
                    self.idxs_signals.get(idx).unwrap(),
                    format_i(coeff),
                )
                .chars(),
            );
        }
        s
    }

    /// Get a nice string represenation of the tuple.
    pub fn format_qeq(&self, (a, b, c): &(Lc, Lc, Lc)) -> String {
        format!(
            "({})({}) = {}",
            self.format_lc(a),
            self.format_lc(b),
            self.format_lc(c)
        )
    }

    /// Check `a * b = c` in this constraint system.
    pub fn check(&self, a: &Lc, b: &Lc, c: &Lc) {
        let av = self.eval(a).unwrap();
        let bv = self.eval(b).unwrap();
        let cv = self.eval(c).unwrap();
        if (av.clone() * &bv) != cv {
            panic!(
                "Error! Bad constraint:\n    {} (value {})\n  * {} (value {})\n  = {} (value {})",
                self.format_lc(a),
                av,
                self.format_lc(b),
                bv,
                self.format_lc(c),
                cv
            )
        }
    }

    fn eval(&self, lc: &Lc) -> Option<FieldV> {
        let ret = self.values.as_ref().map(|values| {
            let mut acc = lc.constant.clone();
            for (var, coeff) in &lc.monomials {
                let val = values
                    .get(var)
                    .expect("Missing value in R1cs::eval")
                    .clone();
                acc += val * coeff;
            }
            acc
        });
        ret
    }
    fn modulus(&self) -> &Integer {
        self.modulus.modulus()
    }

    /// Check all assertions, if values are being tracked.
    pub fn check_all(&self) {
        if self.values.is_some() {
            for (a, b, c) in &self.constraints {
                self.check(a, b, c)
            }
        }
    }

    /// Access the raw constraints.
    pub fn constraints(&self) -> &Vec<(Lc, Lc, Lc)> {
        &self.constraints
    }
}
