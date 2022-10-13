//! Optimizations over R1CS
use super::*;
use crate::util::once::OnceQueue;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use log::debug;

struct LinReducer<S: Eq + Hash> {
    r1cs: R1cs<S>,
    uses: HashMap<usize, HashSet<usize>>,
    queue: OnceQueue<usize>,
    /// The maximum size LC (number of non-constant monomials)
    /// that will be used for propagation
    lc_size_thresh: usize,
}

impl<S: Eq + Hash + Display + Clone> LinReducer<S> {
    fn new(mut r1cs: R1cs<S>, lc_size_thresh: usize) -> Self {
        let uses = LinReducer::gen_uses(&r1cs);
        let queue = (0..r1cs.constraints.len()).collect::<OnceQueue<usize>>();
        for c in &mut r1cs.constraints {
            normalize(c);
        }
        Self {
            r1cs,
            uses,
            queue,
            lc_size_thresh,
        }
    }

    // generate a new uses hash
    fn gen_uses(r1cs: &R1cs<S>) -> HashMap<usize, HashSet<usize>> {
        let mut uses: HashMap<usize, HashSet<usize>> =
            HashMap::with_capacity_and_hasher(r1cs.next_idx, Default::default());
        let mut add = |i: usize, y: &Lc| {
            for x in y.monomials.keys() {
                uses.get_mut(x).map(|m| m.insert(i)).or_else(|| {
                    let mut m: HashSet<usize> = Default::default();
                    m.insert(i);
                    uses.insert(*x, m);
                    None
                });
            }
        };
        for (i, (a, b, c)) in r1cs.constraints.iter().enumerate() {
            add(i, a);
            add(i, b);
            add(i, c);
        }
        uses
    }

    /// Substitute `val` for `var` in constraint with id `con_id`.
    /// Updates uses conservatively (not precisely)
    /// Returns whether a sub happened.
    fn sub_in(&mut self, var: usize, val: &Lc, con_id: usize) -> bool {
        let (a, b, c) = &mut self.r1cs.constraints[con_id];
        let uses = &mut self.uses;
        let mut do_in = |a: &mut Lc| {
            if let Some(sc) = a.monomials.remove(&var) {
                assert_eq!(&a.modulus, &val.modulus);
                a.constant += sc.clone() * &val.constant;
                let tot = a.monomials.len() + val.monomials.len();
                if tot > a.monomials.capacity() {
                    a.monomials.reserve(tot - a.monomials.capacity());
                }
                for (i, v) in &val.monomials {
                    match a.monomials.entry(*i) {
                        Entry::Occupied(mut e) => {
                            let m = e.get_mut();
                            *m += sc.clone() * v;
                            if e.get().is_zero() {
                                uses.get_mut(i).unwrap().remove(&con_id);
                                e.remove_entry();
                            }
                        }
                        Entry::Vacant(e) => {
                            e.insert(sc.clone() * v);
                            uses.get_mut(i).unwrap().insert(con_id);
                        }
                    }
                }
                true
            } else {
                false
            }
        };
        let change_a = do_in(a);
        let change_b = do_in(b);
        let change_c = do_in(c);
        let change = change_a || change_b || change_c;
        self.uses.get_mut(&var).unwrap().remove(&con_id);
        if change {
            normalize(&mut self.r1cs.constraints[con_id]);
        }
        change
    }

    fn clear_constraint(&mut self, i: usize) {
        for v in self.r1cs.constraints[i].0.monomials.keys() {
            self.uses.get_mut(v).unwrap().remove(&i);
        }
        self.r1cs.constraints[i].0.clear();
        for v in self.r1cs.constraints[i].1.monomials.keys() {
            self.uses.get_mut(v).unwrap().remove(&i);
        }
        self.r1cs.constraints[i].1.clear();
        for v in self.r1cs.constraints[i].2.monomials.keys() {
            self.uses.get_mut(v).unwrap().remove(&i);
        }
        self.r1cs.constraints[i].2.clear();
    }

    fn run(mut self) -> R1cs<S> {
        while let Some(con_id) = self.queue.pop() {
            if let Some((var, lc)) =
                as_linear_sub(&self.r1cs.constraints[con_id], &self.r1cs.public_idxs)
            {
                if lc.monomials.len() < self.lc_size_thresh {
                    debug!(
                        "Elim: {} -> {}",
                        self.r1cs.idxs_signals.get(&var).unwrap(),
                        self.r1cs.format_lc(&lc)
                    );
                    self.clear_constraint(con_id);
                    for use_id in self.uses[&var].clone() {
                        if self.sub_in(var, &lc, use_id)
                            && (self.r1cs.constraints[use_id].0.is_zero()
                                || self.r1cs.constraints[use_id].1.is_zero())
                        {
                            self.queue.push(use_id);
                        }
                    }
                    debug_assert_eq!(0, self.uses[&var].len());
                }
            }
        }
        self.r1cs.constraints.retain(|c| !constantly_true(c));
        self.r1cs
    }
}

fn as_linear_sub((a, b, c): &(Lc, Lc, Lc), public: &HashSet<usize>) -> Option<(usize, Lc)> {
    if a.is_zero() || b.is_zero() {
        for i in c.monomials.keys() {
            if !public.contains(i) {
                let mut lc = c.clone();
                let v = lc.monomials.remove(i).unwrap();
                lc *= v.recip();
                return Some((*i, -lc));
            }
        }
        None
    } else {
        None
    }
}

fn normalize((a, b, c): &mut (Lc, Lc, Lc)) {
    match (a.as_const(), b.as_const()) {
        (Some(ac), _) => {
            *c -= &(b.take() * ac);
            a.clear();
        }
        (_, Some(bc)) => {
            *c -= &(a.take() * bc);
            b.clear();
        }
        _ => {}
    }
}

fn constantly_true((a, b, c): &(Lc, Lc, Lc)) -> bool {
    match (a.as_const(), b.as_const(), c.as_const()) {
        (Some(x), Some(y), Some(z)) => (x.clone() * y - z).is_zero(),
        _ => false,
    }
}

/// Attempt to shrink this system by reducing linearities.
///
/// ## Parameters
///
///   * `lc_size_thresh`: the maximum size LC (number of non-constant monomials) that will be used
///   for propagation. `None` means no size limit.
pub fn reduce_linearities<S: Eq + Hash + Clone + Display>(
    r1cs: R1cs<S>,
    lc_size_thresh: Option<usize>,
) -> R1cs<S> {
    LinReducer::new(r1cs, lc_size_thresh.unwrap_or(usize::MAX)).run()
}

#[cfg(test)]
mod test {

    use super::*;

    use fxhash::FxHashMap;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rand::SeedableRng;

    #[derive(Clone, Debug)]
    pub struct SatR1cs(R1cs<String>, FxHashMap<String, Value>);

    impl Arbitrary for SatR1cs {
        fn arbitrary(g: &mut Gen) -> Self {
            let m = 101;
            let field = FieldT::from(Integer::from(m));
            let n_vars = g.size() + 1;
            let vars: Vec<_> = (0..n_vars).map(|i| format!("v{}", i)).collect();
            let mut values: FxHashMap<String, Value> = Default::default();
            let mut r1cs = R1cs::new(field.clone());
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            for v in &vars {
                values.insert(v.clone(), Value::Field(field.random_v(&mut rng)));
                r1cs.add_signal(
                    v.clone(),
                    leaf_term(Op::Var(v.clone(), Sort::Field(field.clone()))),
                );
            }
            for _ in 0..(2 * g.size()) {
                let ac: isize = <isize as Arbitrary>::arbitrary(g) % m;
                let a = if Arbitrary::arbitrary(g) {
                    r1cs.signal_lc(g.choose(&vars[..]).unwrap())
                } else {
                    r1cs.zero()
                } + ac;
                let bc: isize = <isize as Arbitrary>::arbitrary(g) % m;
                let b = if Arbitrary::arbitrary(g) {
                    r1cs.signal_lc(g.choose(&vars[..]).unwrap())
                } else {
                    r1cs.zero()
                } + bc;
                let cc: isize = <isize as Arbitrary>::arbitrary(g) % m;
                let mut c = if Arbitrary::arbitrary(g) {
                    r1cs.signal_lc(g.choose(&vars[..]).unwrap())
                } else {
                    r1cs.zero()
                } + cc;
                let off = r1cs.eval(&a, &values) * r1cs.eval(&b, &values) - r1cs.eval(&c, &values);
                c += &off;
                r1cs.constraint(a, b, c);
            }
            SatR1cs(r1cs, values)
        }
        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let c = self.clone();
            Box::new((0..self.0.constraints.len()).rev().map(move |i| {
                let mut this = c.clone();
                this.0.constraints.truncate(i);
                this
            }))
        }
    }

    #[quickcheck]
    fn random(SatR1cs(r1cs, values): SatR1cs) {
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&values);
    }
}
