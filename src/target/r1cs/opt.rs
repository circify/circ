use super::*;
use std::collections::{HashMap, HashSet, VecDeque};

struct LinReducer<S: Eq + Hash> {
    r1cs: R1cs<S>,
    uses: HashMap<usize, HashSet<usize>>,
    queue: OnceQueue<usize>,
}

struct OnceQueue<T> {
    queue: VecDeque<T>,
    set: HashSet<T>,
}

impl<T: Eq + Hash + Clone> OnceQueue<T> {
    pub fn push(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t)
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front().map(|t| {
            self.set.remove(&t);
            t
        })
    }
    pub fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            set: HashSet::new(),
        }
    }
}

impl<A: Eq + Hash + Clone> std::iter::FromIterator<A> for OnceQueue<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        iter.into_iter().fold(Self::new(), |mut q, i| {
            q.push(i);
            q
        })
    }
}

impl<S: Eq + Hash + Display + Clone> LinReducer<S> {
    fn new(mut r1cs: R1cs<S>) -> Self {
        let sigs: HashSet<usize> = r1cs
            .constraints
            .iter()
            .flat_map(|(a, b, c)| {
                a.monomials
                    .keys()
                    .chain(b.monomials.keys().chain(c.monomials.keys()))
            })
            .cloned()
            .collect();
        let mut uses: HashMap<usize, HashSet<usize>> =
            sigs.into_iter().map(|i| (i, HashSet::new())).collect();
        for (i, (a, b, c)) in r1cs.constraints.iter().enumerate() {
            let mut add = |y: &Lc| {
                for x in y.monomials.keys() {
                    uses.get_mut(x).unwrap().insert(i);
                }
            };
            add(a);
            add(b);
            add(c);
        }
        let queue = (0..r1cs.constraints.len()).collect::<OnceQueue<usize>>();
        for c in &mut r1cs.constraints {
            normalize(c);
        }
        Self { r1cs, uses, queue }
    }

    /// Substitute `val` for `var` in constraint with id `con_id`.
    /// Updates uses conservatively (not precisely)
    /// Returns whether a sub happened.
    fn sub_in(&mut self, var: usize, val: &Lc, con_id: usize) -> bool {
        let (a, b, c) = &mut self.r1cs.constraints[con_id];
        let uses = &mut self.uses;
        let mut do_in = |a: &mut Lc| {
            if let Some(sc) = a.monomials.remove(&var) {
                a.constant += val.constant.clone() * &sc;
                a.constant.rem_floor_assign(&*val.modulus);
                for (i, v) in &val.monomials {
                    match a.monomials.entry(*i) {
                        Entry::Occupied(mut e) => {
                            let m = e.get_mut();
                            *m += v.clone() * &sc;
                            m.rem_floor_assign(&*val.modulus);
                            if e.get() == &Integer::from(0) {
                                uses.get_mut(i).unwrap().remove(&con_id);
                                e.remove_entry();
                            }
                        }
                        Entry::Vacant(e) => {
                            let m = e.insert(v.clone() * &sc);
                            m.rem_floor_assign(&*val.modulus);
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
                self.clear_constraint(con_id);
                for use_id in self.uses[&var].clone() {
                    if self.sub_in(var, &lc, use_id) {
                        if self.r1cs.constraints[use_id].0.is_zero()
                            || self.r1cs.constraints[use_id].1.is_zero()
                        {
                            self.queue.push(use_id);
                        }
                    }
                }
                debug_assert_eq!(0, self.uses[&var].len());
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
                lc *= &(-v.invert(&*lc.modulus).unwrap());
                return Some((*i, lc));
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
        (Some(x), Some(y), Some(z)) => (x.clone() * y - z).rem_floor(&*a.modulus) == 0,
        _ => false,
    }
}

pub fn reduce_linearities<S: Eq + Hash + Clone + Display>(r1cs: R1cs<S>) -> R1cs<S> {
    LinReducer::new(r1cs).run()
}

#[cfg(test)]
mod test {

    use super::*;

    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    #[derive(Clone, Debug)]
    pub struct SatR1cs(R1cs<String>);

    impl Arbitrary for SatR1cs {
        fn arbitrary(g: &mut Gen) -> Self {
            let m = 101;
            let modulus = Integer::from(m);
            let n_vars = g.size() + 1;
            let vars: Vec<_> = (0..n_vars).map(|i| format!("v{}", i)).collect();
            let mut r1cs = R1cs::new(modulus.clone(), true);
            let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
            let s: u32 = Arbitrary::arbitrary(g);
            rug_rng.seed(&Integer::from(s));
            for v in &vars {
                r1cs.add_signal(v.clone(), Some(modulus.clone().random_below(&mut rug_rng)));
            }
            for _ in 0..(2 * g.size()) {
                let mut ac: isize = Arbitrary::arbitrary(g);
                ac.rem_floor_assign(m);
                let a = if Arbitrary::arbitrary(g) {
                    r1cs.signal_lc(g.choose(&vars[..]).unwrap())
                } else {
                    r1cs.zero()
                } + ac;
                let mut bc: isize = Arbitrary::arbitrary(g);
                bc.rem_floor_assign(m);
                let b = if Arbitrary::arbitrary(g) {
                    r1cs.signal_lc(g.choose(&vars[..]).unwrap())
                } else {
                    r1cs.zero()
                } + bc;
                let mut cc: isize = Arbitrary::arbitrary(g);
                cc.rem_floor_assign(m);
                let mut c = if Arbitrary::arbitrary(g) {
                    r1cs.signal_lc(g.choose(&vars[..]).unwrap())
                } else {
                    r1cs.zero()
                } + cc;
                let off = r1cs.eval(&a).unwrap() * r1cs.eval(&b).unwrap() - r1cs.eval(&c).unwrap();
                c += &off;
                r1cs.constraint(a, b, c);
            }
            SatR1cs(r1cs)
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
    fn random(SatR1cs(r1cs): SatR1cs) {
        let r1cs2 = reduce_linearities(r1cs);
        r1cs2.check_all();
    }
}
