//! Rank 1 Constraint Systems

use circ_fields::{FieldT, FieldV};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use log::{debug, trace};
use paste::paste;
use rayon::prelude::*;
use rug::Integer;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::hash::Hash;

use crate::ir::term::*;

#[cfg(feature = "bellman")]
pub mod bellman;
#[cfg(feature = "bellman")]
pub mod mirage;
pub mod opt;
pub mod proof;
#[cfg(feature = "spartan")]
pub mod spartan;
pub mod trans;
pub mod wit_comp;

#[derive(Debug, Clone, Serialize, Deserialize)]
/// A Rank 1 Constraint System.
///
/// Extended to comprehend witness commitments and verifier challenges.
///
/// We view the R1CS relation as R(x, cw_0 .. cw_C, w_0, r_0, w_1, r_1, .. w), where all
/// variables are vectors of field elements and
/// * x is the instance
/// * cw_i is a committed witness
///   * i.e., the commitment is part of the instance, but the data is part of the witness
/// * i from 0 to R is a "round number":
///   * w_i is a witness set by the prover in round i
///   * r_i is a random challenge, sampled as round i ends and round i+1 begins
/// * w is the final round of witnesses
///
/// ## Operations
///
/// To interface with a proof system, it must be able to: (mapping to MIRAGE impl)
/// * get all instance variables (create inputs)
/// * get all committed witness vectors (create witnesses, end blocks)
/// * for each round
///   * get the witness variables (create witnesses, end block)
///   * followed by the challenge variables (create challenges)
/// * get all constraints, and create them
///
/// To interface with a compiler, its must be able to: (mapping to Computation interface)
/// * describe all instance variables in a fixed order (get public variables, fixed order)
/// * describe all committed witness vectors in a fixed order (get witness arrays, fixed order)
/// * for each round
///   * describe the witness variables in that round
///     * (tricky?
///       * since we have deterministic semantics, it suffices to declare the [Computation]
///         witness variables of that round (intermediates are not needed)
///     * )
///   * describe the challenge variables after that round (immediate)
/// * then, we embed the intermediates in w
///
/// To interface with an optimizer, it must be able to
/// * build a variable use-site cache
/// * change constraints/remove them
/// * test whether a variable can be eliminated
///   * x cannot
///   * cw_i cannot
///   * r_i cannot
///   * w_i cannot
///   * w can
/// * since only w variable can be eliminated, there is room for optimizating the contents of w_i
///   * For now, we'll assume that putting the computation witness inputs is sufficient
///
/// Design conclusions:
/// * Since contraints are defined uniformly w.r.t. different kinds of variables, it makes sense
///   for variables to have uniform identifiers. We'll use a [usize].
/// * The compiler seems capable of meeting a very restricted, stateful builder interface.
/// * The optimizer will be happy as long as
///   * there is a uniform variable representation and
///   * it can test that representation for eliminatability
///
/// So, our ultimate data structure is:
/// * a next var counter
/// * a (bi) mapping between variable numbers and names
/// * the builder round we're in
/// * indices defining the blocks:
///   * end of x
///   * for each cw_i: end of i
///   * for each round:
///     * end of w_i
///     * end of r_i
///     * no entry for w
/// * constraints!
/// * terms
///   * variables include:
///     * verifier inputs
///     * prover inputs
///     * challenges
///
/// I'll skip the build interface: it'll map directly to the above.
///
/// The optimizer won't have an interface. It *will* be allowed to remove variables, leaving unused
/// variable numbers.
///
/// The proof system interface:
/// * Setup:
///   * get x: names and numbers (numbers needed to interpret LCs)
///   * for i: get cw_i: "
///   * for i: get w_i and r_i: "
///   * get w
/// * Proving:
///   * Details TBD.
///   * Probably: build an evaluator
///   * evaluator:
///     * submit values (inputs, challenges)
///     * get values
pub struct R1cs {
    modulus: FieldT,
    idx_to_sig: BiMap<Var, String>,
    num_insts: usize,
    num_cwits: Vec<usize>,
    next_cwit: usize,
    round_wit_ends: Vec<usize>,
    next_round_wit: usize,
    round_chall_ends: Vec<usize>,
    next_round_chall: usize,
    num_final_wits: usize,

    challenge_names: Vec<String>,

    /// The contraints themselves
    constraints: Vec<(Lc, Lc, Lc)>,

    /// Terms for computing them.
    #[serde(with = "crate::ir::term::serde_mods::map")]
    terms: HashMap<Var, Term>,
    precompute: precomp::PreComp,
}

/// An assembled R1CS relation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct R1csFinal {
    field: FieldT,
    vars: Vec<Var>,
    constraints: Vec<(Lc, Lc, Lc)>,
    names: HashMap<Var, String>,

    commitments: Vec<Vec<Var>>,
}

/// A variable
#[derive(Hash, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
#[repr(transparent)]
pub struct Var(usize);

impl Var {
    const NUMBER_BITS: u32 = usize::BITS - 3;
    const NUMBER_MASK: usize = !(0b111 << Self::NUMBER_BITS);
    fn new(ty: VarType, number: usize) -> Self {
        assert!(!Self::NUMBER_MASK & number == 0);
        let ty_repr = match ty {
            VarType::Inst => 0b000,
            VarType::CWit => 0b001,
            VarType::RoundWit => 0b010,
            VarType::Chall => 0b011,
            VarType::FinalWit => 0b100,
        };
        Var(ty_repr << Self::NUMBER_BITS | number)
    }
    fn ty(&self) -> VarType {
        match self.0 >> Self::NUMBER_BITS {
            0b000 => VarType::Inst,
            0b001 => VarType::CWit,
            0b010 => VarType::RoundWit,
            0b011 => VarType::Chall,
            0b100 => VarType::FinalWit,
            c => panic!("Bad type code {}", c),
        }
    }
    fn number(&self) -> usize {
        self.0 & Self::NUMBER_MASK
    }
}

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}({})", self.ty(), self.number())
    }
}

#[derive(Debug)]
/// A variable type
pub enum VarType {
    /// x
    Inst,
    /// cw_i
    CWit,
    /// w_i
    RoundWit,
    /// r_i
    Chall,
    /// w
    FinalWit,
}

/// Builder interface
impl R1cs {
    /// Make an empty constraint system, mod `modulus`.
    /// If `values`, then this constraint system will track & expect concrete values.
    pub fn new(modulus: FieldT, precompute: precomp::PreComp) -> Self {
        R1cs {
            modulus,
            idx_to_sig: BiMap::new(),
            num_insts: Default::default(),
            num_cwits: Default::default(),
            next_cwit: Default::default(),
            round_wit_ends: Default::default(),
            next_round_wit: Default::default(),
            round_chall_ends: Default::default(),
            next_round_chall: Default::default(),
            num_final_wits: Default::default(),
            challenge_names: Default::default(),
            constraints: Vec::new(),
            terms: Default::default(),
            precompute,
        }
    }

    fn var(&mut self, s: String, t: Term, ty: VarType) -> Var {
        let id = match ty {
            VarType::Inst => {
                self.num_insts += 1;
                self.num_insts - 1
            }
            VarType::CWit => {
                self.next_cwit += 1;
                self.next_cwit - 1
            }
            VarType::RoundWit => {
                self.next_round_wit += 1;
                self.next_round_wit - 1
            }
            VarType::Chall => {
                self.next_round_chall += 1;
                self.next_round_chall - 1
            }
            VarType::FinalWit => {
                self.num_final_wits += 1;
                self.num_final_wits - 1
            }
        };
        if let VarType::Chall = ty {
            self.challenge_names.push(s.clone());
        }
        let var = Var::new(ty, id);
        // could check `t` dependents
        self.idx_to_sig.insert(var, s);
        self.terms.insert(var, t);
        var
    }

    /// End a round of witnesses and challenges. The challenges will be set after the witnesses.
    pub fn end_round(&mut self) {
        self.round_wit_ends.push(self.next_round_wit);
        self.round_chall_ends.push(self.next_round_chall);
    }

    /// Add a (uncommitted) witness variable.
    #[track_caller]
    pub fn add_var(&mut self, s: String, t: Term, ty: VarType) -> Var {
        assert!(!matches!(ty, VarType::CWit));
        self.var(s, t, ty)
    }

    /// The total number of variables
    pub fn num_vars(&self) -> usize {
        self.num_insts
            + self.next_cwit
            + self.next_round_wit
            + self.next_round_chall
            + self.num_final_wits
    }

    /// Add a vector of committed witness variables
    pub fn add_committed_witness(&mut self, names_and_terms: Vec<(String, Term)>) {
        let n = names_and_terms.len();
        for (name, value) in names_and_terms {
            self.var(name, value, VarType::CWit);
        }
        self.num_cwits.push(n);
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
    pub fn signal_lc(&self, s: &str) -> Lc {
        let idx = self
            .idx_to_sig
            .get_rev(s)
            .expect("Missing signal in signal_lc");
        let mut lc = self.zero();
        lc.monomials.insert(*idx, self.modulus.new_v(1));
        lc
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
                    format_i(coeff),
                    self.idx_to_sig.get_fwd(idx).unwrap(),
                )
                .chars(),
            );
        }
        s
    }

    /// Can this variable be eliminated?
    pub fn can_eliminate(&self, var: Var) -> bool {
        matches!(var.ty(), VarType::FinalWit)
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

impl R1csFinal {
    /// Check `a * b = c` in this constraint system.
    pub fn check(&self, a: &Lc, b: &Lc, c: &Lc, values: &HashMap<Var, FieldV>) {
        let av = self.eval(a, values);
        let bv = self.eval(b, values);
        let cv = self.eval(c, values);
        if (av.clone() * &bv) != cv {
            let mut vars: HashSet<Var> = Default::default();
            vars.extend(a.monomials.keys().copied());
            vars.extend(b.monomials.keys().copied());
            vars.extend(c.monomials.keys().copied());
            for (k, v) in values {
                if vars.contains(k) {
                    eprintln!("  {} -> {}", self.names.get(k).unwrap(), v);
                }
            }
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

    /// Get a nice string represenation of the combination `a`.
    fn format_lc(&self, a: &Lc) -> String {
        let mut s = String::new();

        let half_m: Integer = self.field.modulus().clone() / 2;
        let abs = |i: Integer| {
            if i <= half_m {
                i
            } else {
                self.field.modulus() - i
            }
        };
        let sign = |i: &Integer| if i < &half_m { "+" } else { "-" };
        let format_i = |i: &FieldV| {
            let ii: Integer = i.into();
            format!("{}{}", sign(&ii), abs(ii))
        };

        s.push_str(&format_i(&a.constant));
        for (idx, coeff) in &a.monomials {
            s.extend(format!(" {} {}", format_i(coeff), self.names.get(idx).unwrap()).chars());
        }
        s
    }

    fn eval(&self, lc: &Lc, values: &HashMap<Var, FieldV>) -> FieldV {
        let mut acc = lc.constant.clone();
        for (var, coeff) in &lc.monomials {
            let val = values
                .get(var)
                .unwrap_or_else(|| panic!("Missing value in R1cs::eval for variable {:?}", var))
                .clone();
            acc += val * coeff;
        }
        acc
    }

    /// Check all assertions
    fn check_all(&self, values: &HashMap<Var, FieldV>) {
        self.constraints
            .par_iter()
            .for_each(|(a, b, c)| self.check(a, b, c, values));
    }
}

impl ProverData {
    /// Compute an R1CS witness (setting any challenges to 1s)
    pub fn extend_r1cs_witness(&self, values: &HashMap<String, Value>) -> HashMap<Var, FieldV> {
        // we need to evaluate all R1CS variables
        let mut var_values: HashMap<Var, FieldV> = Default::default();
        let mut eval = wit_comp::StagedWitCompEvaluator::new(&self.precompute);
        // this will hold inputs to the multi-round evaluator.
        let mut inputs = values.clone();
        while var_values.len() < self.r1cs.vars.len() {
            trace!(
                "Have {}/{} values, doing another round",
                var_values.len(),
                self.r1cs.vars.len()
            );
            // do a round of evaluation
            let value_vec = eval.eval_stage(std::mem::take(&mut inputs));
            for value in value_vec {
                trace!(
                    "var {} : {}",
                    self.r1cs
                        .names
                        .get(&self.r1cs.vars[var_values.len()])
                        .unwrap(),
                    value.as_pf()
                );
                var_values.insert(self.r1cs.vars[var_values.len()], value.as_pf().clone());
            }
            // fill the challenges with 1s
            if var_values.len() < self.r1cs.vars.len() {
                for next_var_i in var_values.len()..self.r1cs.vars.len() {
                    if !matches!(self.r1cs.vars[next_var_i].ty(), VarType::Chall) {
                        break;
                    }
                    let var = self.r1cs.vars[next_var_i];
                    let name = self.r1cs.names.get(&var).unwrap().clone();
                    let val = pf_challenge(&name, &self.r1cs.field);
                    var_values.insert(var, val.clone());
                    inputs.insert(name, Value::Field(val));
                }
            }
        }
        var_values
    }
    /// Check all assertions. Puts in 1 for challenges.
    pub fn check_all(&self, values: &HashMap<String, Value>) {
        self.r1cs.check_all(&self.extend_r1cs_witness(values));
    }

    /// How many commitments?
    pub fn num_commitments(&self) -> usize {
        self.r1cs.commitments.len()
    }
}

/// A bidirectional map.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct BiMap<S: Hash + Eq + Clone, T: Hash + Eq + Clone> {
    fwd: HashMap<S, T>,
    rev: HashMap<T, S>,
}

#[allow(dead_code)]
impl<S: Hash + Eq + Clone + Debug, T: Hash + Eq + Clone + Debug> BiMap<S, T> {
    fn new() -> Self {
        Self {
            fwd: Default::default(),
            rev: Default::default(),
        }
    }
    fn len(&self) -> usize {
        debug_assert_eq!(self.fwd.len(), self.rev.len());
        self.fwd.len()
    }
    #[allow(clippy::uninlined_format_args)]
    fn insert(&mut self, s: S, t: T) {
        assert!(
            self.fwd.insert(s.clone(), t.clone()).is_none(),
            "Duplicate key {:?}",
            s
        );
        assert!(
            self.rev.insert(t.clone(), s).is_none(),
            "Duplicate value {:?}",
            t
        );
    }
    fn contains_key<Q>(&self, s: &Q) -> bool
    where
        S: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.fwd.contains_key(s)
    }
    fn get_fwd<Q>(&self, s: &Q) -> Option<&T>
    where
        S: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.fwd.get(s)
    }
    fn get_rev<Q>(&self, t: &Q) -> Option<&S>
    where
        T: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.rev.get(t)
    }
    fn remove_fwd<Q: std::borrow::Borrow<S>>(&mut self, s: &Q) {
        let t = self.fwd.remove(s.borrow()).unwrap();
        self.rev.remove(&t).unwrap();
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
/// The type of a signal
pub enum SigTy {
    /// Known by all parties, initially
    Instance,
    /// Known by the prover
    Witness,
    /// Randomly sampled
    Challenge,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
/// A linear combination
pub struct Lc {
    modulus: FieldT,
    constant: FieldV,
    monomials: HashMap<Var, FieldV>,
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
                            std::collections::hash_map::Entry::Occupied(mut e) => {
                                e.get_mut().[<$fn _assign>](v);
                                if e.get().is_zero() {
                                    e.remove_entry();
                                }
                            }
                            std::collections::hash_map::Entry::Vacant(e) => {
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

impl R1cs {
    /// Check `a * b = c` in this constraint system.
    pub fn check(&self, a: &Lc, b: &Lc, c: &Lc, values: &HashMap<Var, FieldV>) {
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

    fn eval(&self, lc: &Lc, values: &HashMap<Var, FieldV>) -> FieldV {
        let mut acc = lc.constant.clone();
        for (var, coeff) in &lc.monomials {
            let val = values
                .get(var)
                .unwrap_or_else(|| panic!("Missing value in R1cs::eval for variable {:?}", var))
                .clone();
            acc += val * coeff;
        }
        acc
    }

    fn eval_all_vars(&self, inputs: &HashMap<String, Value>) -> HashMap<Var, FieldV> {
        let after_precompute = self.precompute.eval(inputs);
        let mut cache = Default::default();
        self.terms
            .iter()
            .map(|(var, term)| {
                let val = eval_cached(term, &after_precompute, &mut cache);
                if let Value::Field(f) = val {
                    (*var, f.clone())
                } else {
                    panic!("Non-field");
                }
            })
            .collect()
    }

    /// Check all assertions, if values are being tracked.
    pub fn check_all(&self, inputs: &HashMap<String, Value>) {
        let var_values = self.eval_all_vars(inputs);
        for (a, b, c) in &self.constraints {
            self.check(a, b, c, &var_values)
        }
    }

    fn insts_iter(&self) -> impl Iterator<Item = Var> + '_ {
        (0..self.num_insts)
            .map(|i| Var::new(VarType::Inst, i))
            .filter(move |v| self.idx_to_sig.contains_key(v))
    }

    fn final_wits_iter(&self) -> impl Iterator<Item = Var> + '_ {
        (0..self.num_final_wits)
            .map(|i| Var::new(VarType::FinalWit, i))
            .filter(move |v| self.idx_to_sig.contains_key(v))
    }

    fn cwits_iter(&self) -> impl Iterator<Item = Var> + '_ {
        (0..self.next_cwit)
            .map(|i| Var::new(VarType::CWit, i))
            .filter(move |v| self.idx_to_sig.contains_key(v))
    }

    fn cwits(&self) -> Vec<Vec<Var>> {
        let mut i = 0;
        self.num_cwits
            .iter()
            .map(|len| {
                (0..*len)
                    .map(|_| {
                        i += 1;
                        Var::new(VarType::CWit, i - 1)
                    })
                    .collect()
            })
            .collect()
    }

    fn challs_iter(&self, round: usize) -> impl Iterator<Item = Var> + '_ {
        let start = if round == 0 {
            0
        } else {
            self.round_chall_ends[round - 1]
        };
        let end = self.round_chall_ends[round];
        (start..end)
            .map(|i| Var::new(VarType::Chall, i))
            .filter(move |v| self.idx_to_sig.contains_key(v))
    }

    fn round_wits_iter(&self, round: usize) -> impl Iterator<Item = Var> + '_ {
        let start = if round == 0 {
            0
        } else {
            self.round_wit_ends[round - 1]
        };
        let end = self.round_wit_ends[round];
        (start..end)
            .map(|i| Var::new(VarType::RoundWit, i))
            .filter(move |v| self.idx_to_sig.contains_key(v))
    }

    /// Returns a list of (signal list, challenge list) pairs.
    /// The prove computes the values of signals.
    /// The proof system computes the values of challenges.
    /// All signals are computed from (a) prover inputs and (b) challenge values.
    fn stage_vars(&self) -> Vec<(Vec<Var>, Vec<Var>)> {
        let mut out = Vec::new();
        out.push((
            self.insts_iter().chain(self.cwits_iter()).collect(),
            Vec::new(),
        ));
        for round_idx in 0..self.round_chall_ends.len() {
            out.push((
                self.round_wits_iter(round_idx).collect(),
                self.challs_iter(round_idx).collect(),
            ));
        }
        out.push((self.final_wits_iter().collect(), Vec::new()));
        out
    }

    /// Prover Data
    fn prover_data(self, cs: &Computation) -> ProverData {
        let mut precompute = cs.precomputes.clone();
        self.extend_precomputation(&mut precompute, false);
        // we still need to remove the non-r1cs variables
        //use crate::ir::proof::PROVER_ID;
        //let all_inputs = cs.metadata.get_inputs_for_party(Some(PROVER_ID));
        let mut precompute_map = precompute.flatten();
        let mut vars: HashMap<String, Sort> = {
            PostOrderIter::from_roots_and_skips(
                precompute_map.values().cloned(),
                Default::default(),
            )
            .filter_map(|t| {
                if let Op::Var(n, s) = t.op() {
                    Some((n.clone(), s.clone()))
                } else {
                    None
                }
            })
            .collect()
        };
        for c in &self.challenge_names {
            vars.remove(c);
        }
        let mut comp = wit_comp::StagedWitComp::default();
        let mut var_sequence = Vec::new();
        for (computed_in_stage, challs) in self.stage_vars() {
            let terms = computed_in_stage
                .iter()
                .map(|v| {
                    let name = self.idx_to_sig.get_fwd(v).unwrap();
                    precompute_map.remove(name).unwrap()
                })
                .collect();
            comp.add_stage(std::mem::take(&mut vars), terms);
            vars = challs
                .iter()
                .map(|cvar| {
                    (
                        self.idx_to_sig.get_fwd(cvar).unwrap().clone(),
                        Sort::Field(self.modulus.clone()),
                    )
                })
                .collect();
            var_sequence.extend(computed_in_stage);
            var_sequence.extend(challs);
        }

        ProverData {
            r1cs: R1csFinal {
                field: self.modulus.clone(),
                names: var_sequence
                    .iter()
                    .map(|v| (*v, self.idx_to_sig.get_fwd(v).unwrap().clone()))
                    .collect(),
                vars: var_sequence,
                commitments: self.cwits(),
                constraints: self.constraints,
            },
            precompute: comp,
        }
    }

    /// Prover Data
    fn verifier_data(&self, cs: &Computation) -> VerifierData {
        let mut precompute = cs.precomputes.clone();
        self.extend_precomputation(&mut precompute, true);
        let public_inputs = cs.metadata.get_inputs_for_party(None);
        precompute.restrict_to_inputs(public_inputs);
        let vars: HashMap<String, Sort> = {
            PostOrderIter::new(precompute.tuple())
                .filter_map(|t| {
                    if let Op::Var(n, s) = t.op() {
                        Some((n.clone(), s.clone()))
                    } else {
                        None
                    }
                })
                .collect()
        };
        for c in &self.challenge_names {
            assert!(!vars.contains_key(c));
        }
        let mut precompute_map = precompute.flatten();
        let terms = self
            .insts_iter()
            .map(|v| {
                let name = self.idx_to_sig.get_fwd(&v).unwrap();
                precompute_map.remove(name).unwrap()
            })
            .collect();
        let mut comp = wit_comp::StagedWitComp::default();
        comp.add_stage(vars, terms);
        VerifierData {
            precompute: comp,
            num_commitments: self.num_cwits.len(),
        }
    }

    /// Add the signals of this R1CS instance to the precomputation.
    fn extend_precomputation(&self, precompute: &mut precomp::PreComp, public_signals_only: bool) {
        for (var, term) in &self.terms {
            if !matches!(var.ty(), VarType::Chall)
                && (!public_signals_only || matches!(var.ty(), VarType::Inst | VarType::CWit))
            {
                let sig_name = self.idx_to_sig.get_fwd(var).unwrap();
                if !precompute.outputs().contains_key(sig_name) {
                    precompute.add_output(sig_name.clone(), term.clone());
                }
            }
        }
    }

    /// Split this R1CS into prover (Proving, Setup) and verifier (Verifying) information.
    pub fn finalize(self, cs: &Computation) -> (ProverData, VerifierData) {
        let vd = self.verifier_data(cs);
        let pd = self.prover_data(cs);
        (pd, vd)
    }

    /// Get an IR term that represents this system.
    pub fn lc_ir_term(&self, lc: &Lc) -> Term {
        term(PF_ADD,
            std::iter::once(pf_lit(lc.constant.clone())).chain(lc.monomials.iter().map(|(i, coeff)| term![PF_MUL; pf_lit(coeff.clone()), leaf_term(Op::Var(self.idx_to_sig.get_fwd(i).unwrap().into(), Sort::Field(self.modulus.clone())))])).collect())
    }

    /// Get an IR term that represents this system.
    pub fn ir_term(&self) -> Term {
        term(AND,
        self.constraints.iter().map(|(a, b, c)|
            term![EQ; term![PF_MUL; self.lc_ir_term(a), self.lc_ir_term(b)], self.lc_ir_term(c)]).collect())
    }
}

impl VerifierData {
    /// Given verifier inputs, compute a vector of field values to feed to the proof system.
    pub fn eval(&self, value_map: &HashMap<String, Value>) -> Vec<FieldV> {
        let mut eval = wit_comp::StagedWitCompEvaluator::new(&self.precompute);
        eval.eval_stage(value_map.clone())
            .into_iter()
            .map(|v| v.as_pf().clone())
            .collect()
    }

    /// How many commitments?
    pub fn num_commitments(&self) -> usize {
        self.num_commitments
    }
}

/// Relation-related data that a prover needs to make a proof.
#[derive(Debug, Serialize, Deserialize)]
pub struct ProverData {
    /// R1cs
    pub r1cs: R1csFinal,
    /// Witness computation
    pub precompute: wit_comp::StagedWitComp,
}

/// Relation-related data that a verifier needs to check a proof.
#[derive(Debug, Serialize, Deserialize)]
pub struct VerifierData {
    /// Instance computation
    pub precompute: wit_comp::StagedWitComp,
    /// How many commitments in this predicate?
    num_commitments: usize,
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
