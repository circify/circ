//! Rank 1 Constraint Systems

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use log::debug;
use rug::ops::{RemRounding, RemRoundingAssign};
use rug::Integer;
use std::collections::hash_map::Entry;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;

pub mod bellman;
pub mod opt;
pub mod trans;

#[derive(Clone, Debug)]
/// A Rank 1 Constraint System.
pub struct R1cs<S: Hash + Eq> {
    modulus: Rc<Integer>,
    signal_idxs: HashMap<S, usize>,
    idxs_signals: HashMap<usize, S>,
    next_idx: usize,
    public_idxs: HashSet<usize>,
    values: Option<HashMap<usize, Integer>>,
    constraints: Vec<(Lc, Lc, Lc)>,
}

#[derive(Clone, Debug)]
/// A linear combination
pub struct Lc {
    modulus: Rc<Integer>,
    constant: Integer,
    monomials: HashMap<usize, Integer>,
}

impl Lc {
    /// Is this the zero combination?
    pub fn is_zero(&self) -> bool {
        self.monomials.is_empty() && self.constant == 0
    }
    /// Make this the zero combination.
    pub fn clear(&mut self) {
        self.monomials.clear();
        self.constant = Integer::from(0);
    }
    /// Take this linear combination, leaving zero in its place.
    pub fn take(&mut self) -> Self {
        let monomials = std::mem::take(&mut self.monomials);
        let constant = std::mem::take(&mut self.constant);
        Self {
            monomials,
            constant,
            modulus: self.modulus.clone(),
        }
    }
    /// Is this a constant? If so, return that constant.
    pub fn as_const(&self) -> Option<&Integer> {
        self.monomials.is_empty().then(|| &self.constant)
    }
}

impl std::ops::Add<&Lc> for Lc {
    type Output = Lc;
    fn add(mut self, other: &Lc) -> Lc {
        self += other;
        self
    }
}

impl std::ops::AddAssign<&Lc> for Lc {
    fn add_assign(&mut self, other: &Lc) {
        assert_eq!(&self.modulus, &other.modulus);
        self.constant += &other.constant;
        self.constant.rem_floor_assign(&*self.modulus);
        for (i, v) in &other.monomials {
            match self.monomials.entry(*i) {
                Entry::Occupied(mut e) => {
                    let m = e.get_mut();
                    *m += v;
                    m.rem_floor_assign(&*other.modulus);
                    if e.get() == &Integer::from(0) {
                        e.remove_entry();
                    }
                }
                Entry::Vacant(e) => {
                    e.insert(v.clone());
                }
            }
        }
    }
}

impl std::ops::Add<&Integer> for Lc {
    type Output = Lc;
    fn add(mut self, other: &Integer) -> Lc {
        self += other;
        self
    }
}

impl std::ops::AddAssign<&Integer> for Lc {
    fn add_assign(&mut self, other: &Integer) {
        self.constant += other;
        self.constant.rem_floor_assign(&*self.modulus);
    }
}

impl std::ops::Add<isize> for Lc {
    type Output = Lc;
    fn add(mut self, other: isize) -> Lc {
        self += other;
        self
    }
}

impl std::ops::AddAssign<isize> for Lc {
    fn add_assign(&mut self, other: isize) {
        self.constant += Integer::from(other);
        self.constant.rem_floor_assign(&*self.modulus);
    }
}

impl std::ops::Sub<&Lc> for Lc {
    type Output = Lc;
    fn sub(mut self, other: &Lc) -> Lc {
        self -= other;
        self
    }
}

impl std::ops::SubAssign<&Lc> for Lc {
    fn sub_assign(&mut self, other: &Lc) {
        assert_eq!(&self.modulus, &other.modulus);
        self.constant -= &other.constant;
        self.constant.rem_floor_assign(&*self.modulus);
        for (i, v) in &other.monomials {
            match self.monomials.entry(*i) {
                Entry::Occupied(mut e) => {
                    let m = e.get_mut();
                    *m -= v;
                    m.rem_floor_assign(&*other.modulus);
                    if e.get() == &Integer::from(0) {
                        e.remove_entry();
                    }
                }
                Entry::Vacant(e) => {
                    let m = e.insert(-v.clone());
                    m.rem_floor_assign(&*other.modulus);
                }
            }
        }
    }
}

impl std::ops::Sub<&Integer> for Lc {
    type Output = Lc;
    fn sub(mut self, other: &Integer) -> Lc {
        self -= other;
        self
    }
}

impl std::ops::SubAssign<&Integer> for Lc {
    fn sub_assign(&mut self, other: &Integer) {
        self.constant -= other;
        self.constant.rem_floor_assign(&*self.modulus);
    }
}

impl std::ops::Sub<isize> for Lc {
    type Output = Lc;
    fn sub(mut self, other: isize) -> Lc {
        self -= other;
        self
    }
}

impl std::ops::SubAssign<isize> for Lc {
    fn sub_assign(&mut self, other: isize) {
        self.constant -= Integer::from(other);
        self.constant.rem_floor_assign(&*self.modulus);
    }
}

impl std::ops::Neg for Lc {
    type Output = Lc;
    fn neg(mut self) -> Lc {
        self.constant = -self.constant;
        self.constant.rem_floor_assign(&*self.modulus);
        for v in &mut self.monomials.values_mut() {
            *v *= Integer::from(-1);
            v.rem_floor_assign(&*self.modulus);
        }
        self
    }
}

impl std::ops::Mul<&Integer> for Lc {
    type Output = Lc;
    fn mul(mut self, other: &Integer) -> Lc {
        self *= other;
        self
    }
}

impl std::ops::MulAssign<&Integer> for Lc {
    fn mul_assign(&mut self, other: &Integer) {
        self.constant *= other;
        self.constant.rem_floor_assign(&*self.modulus);
        if other == &Integer::from(0) {
            self.monomials.clear();
        } else {
            for v in &mut self.monomials.values_mut() {
                *v *= other;
                v.rem_floor_assign(&*self.modulus);
            }
        }
    }
}

impl std::ops::Mul<isize> for Lc {
    type Output = Lc;
    fn mul(mut self, other: isize) -> Lc {
        self *= other;
        self
    }
}

impl std::ops::MulAssign<isize> for Lc {
    fn mul_assign(&mut self, other: isize) {
        self.constant *= Integer::from(other);
        self.constant.rem_floor_assign(&*self.modulus);
        if other == 0 {
            self.monomials.clear();
        } else {
            for v in &mut self.monomials.values_mut() {
                *v *= Integer::from(other);
                v.rem_floor_assign(&*self.modulus);
            }
        }
    }
}

impl<S: Clone + Hash + Eq + Display> R1cs<S> {
    /// Make an empty constraint system, mod `modulus`.
    /// If `values`, then this constraint system will track & expect concrete values.
    pub fn new(modulus: Integer, values: bool) -> Self {
        R1cs {
            modulus: Rc::new(modulus),
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
            constant: Integer::from(0),
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
        lc.monomials.insert(*idx, Integer::from(1));
        lc
    }
    /// Create a new wire, `s`. If this system is tracking concrete values, you must provide the
    /// value, `v`.
    pub fn add_signal(&mut self, s: S, v: Option<Integer>) {
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
        let abs = |i: &Integer| {
            if i < &half_m {
                i.clone()
            } else {
                self.modulus() - i.clone()
            }
        };
        let sign = |i: &Integer| if i < &half_m { "+" } else { "-" };
        let format_i = |i: &Integer| format!("{}{}", sign(i), abs(i));

        s.push_str(&format_i(&Integer::from(&a.constant)));
        for (idx, coeff) in &a.monomials {
            s.extend(
                format!(
                    " {} {}{}",
                    sign(coeff),
                    abs(coeff),
                    self.idxs_signals.get(idx).unwrap(),
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
        if (av.clone() * &bv).rem_floor(&*self.modulus) != cv {
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

    fn eval(&self, lc: &Lc) -> Option<Integer> {
        self.values.as_ref().map(|values| {
            let mut acc = lc.constant.clone();
            for (var, coeff) in &lc.monomials {
                let val = values
                    .get(var)
                    .expect("Missing value in R1cs::eval")
                    .clone();
                acc += val * coeff;
                acc.rem_floor_assign(&*self.modulus);
            }
            acc
        })
    }
    fn modulus(&self) -> &Integer {
        &self.modulus
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
