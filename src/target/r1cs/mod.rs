//! Rank 1 Constraint Systems

use circ_fields::{FieldT, FieldV};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use log::debug;
use paste::paste;
use rug::Integer;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::hash_map::Entry;
use std::fmt::Display;
use std::hash::Hash;

use crate::ir::term::*;

#[cfg(feature = "r1cs")]
pub mod bellman;
pub mod opt;
#[cfg(feature = "r1cs")]
pub mod spartan;
pub mod trans;

#[derive(Debug, Clone, Serialize, Deserialize)]
/// A Rank 1 Constraint System.
pub struct R1cs<S: Hash + Eq> {
    modulus: FieldT,
    signal_idxs: HashMap<S, usize>,
    idxs_signals: HashMap<usize, S>,
    next_idx: usize,
    public_idxs: HashSet<usize>,
    constraints: Vec<(Lc, Lc, Lc)>,
    #[serde(
        deserialize_with = "deserialize_term_vec",
        serialize_with = "serialize_term_vec"
    )]
    terms: Vec<Term>,
}

// serde requires a specific signature here.
#[allow(clippy::ptr_arg)]
fn serialize_term_vec<S>(ts: &Vec<Term>, s: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    term(Op::Tuple, ts.clone()).serialize(s)
}

fn deserialize_term_vec<'de, D>(d: D) -> Result<Vec<Term>, D::Error>
where
    D: Deserializer<'de>,
{
    let tuple: Term = Deserialize::deserialize(d)?;
    Ok(tuple.cs.clone())
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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
        self.monomials.is_empty().then_some(&self.constant)
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
    pub fn new(modulus: FieldT) -> Self {
        R1cs {
            modulus,
            signal_idxs: HashMap::default(),
            idxs_signals: HashMap::default(),
            next_idx: 0,
            public_idxs: HashSet::default(),
            constraints: Vec::new(),
            terms: Vec::new(),
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
    ///
    /// You must also provide `term`, that computes the signal value from *some* inputs.
    pub fn add_signal(&mut self, s: S, term: Term) {
        let n = self.next_idx;
        self.next_idx += 1;
        self.signal_idxs.insert(s.clone(), n);
        self.idxs_signals.insert(n, s);
        assert_eq!(n, self.terms.len());
        self.terms.push(term);
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
        self.constraints.push((a, b, c));
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

    fn modulus(&self) -> &Integer {
        self.modulus.modulus()
    }

    /// Access the raw constraints.
    pub fn constraints(&self) -> &Vec<(Lc, Lc, Lc)> {
        &self.constraints
    }
}

impl R1cs<String> {
    /// Check `a * b = c` in this constraint system.
    pub fn check(&self, a: &Lc, b: &Lc, c: &Lc, values: &HashMap<String, Value>) {
        let av = self.eval(a, values);
        let bv = self.eval(b, values);
        let cv = self.eval(c, values);
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

    fn eval(&self, lc: &Lc, values: &HashMap<String, Value>) -> FieldV {
        let mut acc = lc.constant.clone();
        for (var, coeff) in &lc.monomials {
            let name = self.idxs_signals.get(var).unwrap();
            let val = values
                .get(name)
                .unwrap_or_else(|| panic!("Missing value in R1cs::eval for variable {}", name))
                .as_pf()
                .clone();
            acc += val * coeff;
        }
        acc
    }

    /// Check all assertions, if values are being tracked.
    pub fn check_all(&self, values: &HashMap<String, Value>) {
        for (a, b, c) in &self.constraints {
            self.check(a, b, c, values)
        }
    }

    /// Add the signals of this R1CS instance to the precomputation.
    fn extend_precomputation(&self, precompute: &mut precomp::PreComp, public_signals_only: bool) {
        for i in 0..self.next_idx {
            let sig_name = self.idxs_signals.get(&i).unwrap();
            if (!public_signals_only || self.public_idxs.contains(&i))
                && !precompute.outputs().contains_key(sig_name)
            {
                let term = self.terms[i].clone();
                precompute.add_output(sig_name.clone(), term);
            }
        }
    }

    /// Compute the verifier data for this R1CS relation, given a precomputation
    /// that computes the variables that are relation inputs
    pub fn verifier_data(&self, cs: &Computation) -> VerifierData {
        let mut precompute = cs.precomputes.clone();
        self.extend_precomputation(&mut precompute, true);
        let public_inputs = cs.metadata.get_inputs_for_party(None);
        precompute.restrict_to_inputs(public_inputs);
        let pf_input_order: Vec<String> = (0..self.next_idx)
            .filter(|i| self.public_idxs.contains(i))
            .map(|i| self.idxs_signals.get(&i).cloned().unwrap())
            .collect();
        let mut precompute_inputs = HashMap::default();
        for input in &pf_input_order {
            if let Some(output_term) = precompute.outputs().get(input) {
                for (v, s) in extras::free_variables_with_sorts(output_term.clone()) {
                    precompute_inputs.insert(v, s);
                }
            } else {
                precompute_inputs.insert(input.clone(), Sort::Field(self.modulus.clone()));
            }
        }
        VerifierData {
            precompute_inputs,
            precompute,
            pf_input_order,
        }
    }

    /// Compute the verifier data for this R1CS relation, given a precomputation
    /// that computes the variables that are relation inputs
    pub fn prover_data(&self, cs: &Computation) -> ProverData {
        let mut precompute = cs.precomputes.clone();
        self.extend_precomputation(&mut precompute, false);
        // we still need to remove the non-r1cs variables
        use crate::ir::proof::PROVER_ID;
        let all_inputs = cs.metadata.get_inputs_for_party(Some(PROVER_ID));
        precompute.restrict_to_inputs(all_inputs);
        let pf_input_order: Vec<String> = (0..self.next_idx)
            .filter(|i| self.public_idxs.contains(i))
            .map(|i| self.idxs_signals.get(&i).cloned().unwrap())
            .collect();
        let mut precompute_inputs = HashMap::default();
        for input in &pf_input_order {
            if let Some(output_term) = precompute.outputs().get(input) {
                for (v, s) in extras::free_variables_with_sorts(output_term.clone()) {
                    precompute_inputs.insert(v, s);
                }
            } else {
                precompute_inputs.insert(input.clone(), Sort::Field(self.modulus.clone()));
            }
        }
        for o in precompute.outputs().keys() {
            precompute_inputs.remove(o);
        }
        ProverData {
            precompute_inputs,
            precompute,
            r1cs: self.clone(),
        }
    }

    /// Get an IR term that represents this system.
    pub fn lc_ir_term(&self, lc: &Lc) -> Term {
        term(PF_ADD,
            std::iter::once(pf_lit(lc.constant.clone())).chain(lc.monomials.iter().map(|(i, coeff)| term![PF_MUL; pf_lit(coeff.clone()), leaf_term(Op::Var(self.idxs_signals.get(i).unwrap().into(), Sort::Field(self.modulus.clone())))])).collect())
    }

    /// Get an IR term that represents this system.
    pub fn ir_term(&self) -> Term {
        term(AND,
        self.constraints.iter().map(|(a, b, c)|
            term![EQ; term![PF_MUL; self.lc_ir_term(a), self.lc_ir_term(b)], self.lc_ir_term(c)]).collect())
    }
}

/// Relation-related data that a verifier needs to check a proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifierData {
    /// Inputs that the verifier must have
    pub precompute_inputs: HashMap<String, Sort>,
    /// A precomputation to perform on those inputs
    pub precompute: precomp::PreComp,
    /// The order in which the outputs must be fed into the proof system
    pub pf_input_order: Vec<String>,
}

impl VerifierData {
    /// Given verifier inputs, compute a vector of integers to feed to the proof system.
    pub fn eval(&self, value_map: &HashMap<String, Value>) -> Vec<rug::Integer> {
        for (input, sort) in &self.precompute_inputs {
            let value = value_map
                .get(input)
                .unwrap_or_else(|| panic!("No input for {}", input));
            let sort2 = value.sort();
            assert_eq!(
                sort, &sort2,
                "Sort mismatch for {}. Expected\n\t{} but got\n\t{}",
                input, sort, sort2
            );
        }
        let new_map = self.precompute.eval(value_map);
        self.pf_input_order
            .iter()
            .map(|input| {
                new_map
                    .get(input)
                    .unwrap_or_else(|| panic!("Missing input {}", input))
                    .as_pf()
                    .i()
            })
            .collect()
    }
}

/// Relation-related data that a prover needs to check a proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverData {
    /// The R1CS instance.
    pub r1cs: R1cs<String>,
    /// Inputs that the verifier must have
    pub precompute_inputs: HashMap<String, Sort>,
    /// A precomputation to perform on those inputs
    pub precompute: precomp::PreComp,
}

#[derive(Clone, Debug)]
/// A linear combination with an attached prime-field term that computes its variable
pub struct TermLc(pub Term, pub Lc);

impl TermLc {
    /// Is this the zero combination?
    pub fn is_zero(&self) -> bool {
        self.1.is_zero()
    }
    /// Make this the zero combination.
    pub fn clear(&mut self) {
        self.1.clear();
        self.0 = pf_lit(self.field().new_v(0u8));
    }
    /// Take this linear combination, leaving zero in its place.
    pub fn take(&mut self) -> Self {
        let lc = self.1.take();
        let zero_t = pf_lit(self.field().new_v(0u8));
        let t = std::mem::replace(&mut self.0, zero_t);
        TermLc(t, lc)
    }
    /// Is this a constant? If so, return that constant.
    pub fn as_const(&self) -> Option<&FieldV> {
        self.1.as_const()
    }
    /// Get the field type for this term & linear combination.
    pub fn field(&self) -> FieldT {
        self.1.modulus.clone()
    }
}

impl std::ops::Add<&TermLc> for TermLc {
    type Output = TermLc;
    fn add(mut self, other: &TermLc) -> TermLc {
        self += other;
        self
    }
}

impl std::ops::AddAssign<&TermLc> for TermLc {
    fn add_assign(&mut self, other: &TermLc) {
        self.1 += &other.1;
        self.0 = term![PF_ADD; self.0.clone(), other.0.clone()];
    }
}

impl std::ops::Add<&FieldV> for TermLc {
    type Output = TermLc;
    fn add(mut self, other: &FieldV) -> TermLc {
        self.0 = term![PF_ADD; self.0.clone(), pf_lit(other.clone())];
        self.1 += other;
        self
    }
}

impl std::ops::AddAssign<&FieldV> for TermLc {
    fn add_assign(&mut self, other: &FieldV) {
        self.0 = term![PF_ADD; self.0.clone(), pf_lit(other.clone())];
        self.1 += other;
    }
}

impl std::ops::Add<isize> for TermLc {
    type Output = TermLc;
    fn add(mut self, other: isize) -> TermLc {
        self += other;
        self
    }
}

impl std::ops::AddAssign<isize> for TermLc {
    fn add_assign(&mut self, other: isize) {
        self.1 += other;
        self.0 = term![PF_ADD; self.0.clone(), pf_lit(self.field().new_v(other))];
    }
}

impl std::ops::Sub<&TermLc> for TermLc {
    type Output = TermLc;
    fn sub(mut self, other: &TermLc) -> TermLc {
        self -= other;
        self
    }
}

impl std::ops::SubAssign<&TermLc> for TermLc {
    fn sub_assign(&mut self, other: &TermLc) {
        self.1 -= &other.1;
        self.0 = term![PF_ADD; self.0.clone(), term![PF_NEG; other.0.clone()]];
    }
}

impl std::ops::Sub<&FieldV> for TermLc {
    type Output = TermLc;
    fn sub(mut self, other: &FieldV) -> TermLc {
        self.0 = term![PF_ADD; self.0.clone(), term![PF_NEG; pf_lit(other.clone())]];
        self.1 -= other;
        self
    }
}

impl std::ops::SubAssign<&FieldV> for TermLc {
    fn sub_assign(&mut self, other: &FieldV) {
        self.0 = term![PF_ADD; self.0.clone(), term![PF_NEG; pf_lit(other.clone())]];
        self.1 -= other;
    }
}

impl std::ops::Sub<isize> for TermLc {
    type Output = TermLc;
    fn sub(mut self, other: isize) -> TermLc {
        self -= other;
        self
    }
}

impl std::ops::SubAssign<isize> for TermLc {
    fn sub_assign(&mut self, other: isize) {
        self.1 -= other;
        self.0 = term![PF_ADD; self.0.clone(), term![PF_NEG; pf_lit(self.field().new_v(other))]];
    }
}

impl std::ops::Neg for TermLc {
    type Output = TermLc;
    fn neg(mut self) -> TermLc {
        self.1 = -self.1;
        self.0 = term![PF_NEG; self.0];
        self
    }
}

impl std::ops::Mul<&FieldV> for TermLc {
    type Output = TermLc;
    fn mul(mut self, other: &FieldV) -> TermLc {
        self *= other;
        self
    }
}

impl std::ops::MulAssign<&FieldV> for TermLc {
    fn mul_assign(&mut self, other: &FieldV) {
        self.1 *= other;
        self.0 = term![PF_MUL; self.0.clone(), pf_lit(other.clone())];
    }
}

impl std::ops::Mul<isize> for TermLc {
    type Output = TermLc;
    fn mul(mut self, other: isize) -> TermLc {
        self *= other;
        self
    }
}

impl std::ops::MulAssign<isize> for TermLc {
    fn mul_assign(&mut self, other: isize) {
        self.1 *= other;
        self.0 = term![PF_MUL; self.0.clone(), pf_lit(self.field().new_v(other))];
    }
}
