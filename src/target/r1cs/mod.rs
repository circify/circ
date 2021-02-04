use rug::Integer;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::rc::Rc;

pub struct R1cs<S: Hash + Eq> {
    modulus: Rc<Integer>,
    signal_idxs: HashMap<S, usize>,
    idxs_signals: HashMap<usize, HashSet<S>>,
    next_idx: usize,
    public_idxs: HashSet<usize>,
    values: Option<HashMap<usize, Integer>>,
    constraints: Vec<(Lc, Lc, Lc)>,
}

#[derive(Clone)]
pub struct Lc {
    modulus: Rc<Integer>,
    constant: Integer,
    monomials: HashMap<usize, Integer>,
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
        self.constant %= &*self.modulus;
        for (i, v) in &other.monomials {
            self.monomials
                .entry(*i)
                .and_modify(|u| {
                    *u += v;
                    *u %= &*other.modulus;
                })
                .or_insert_with(|| v.clone());
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
        self.constant %= &*self.modulus;
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
        self.constant %= &*self.modulus;
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
        self.constant %= &*self.modulus;
        for (i, v) in &other.monomials {
            self.monomials
                .entry(*i)
                .and_modify(|u| {
                    *u -= v;
                    *u %= &*other.modulus;
                })
                .or_insert_with(|| v.clone());
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
        self.constant %= &*self.modulus;
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
        self.constant %= &*self.modulus;
    }
}

impl std::ops::Neg for Lc {
    type Output = Lc;
    fn neg(mut self) -> Lc {
        self.constant = -self.constant;
        self.constant %= &*self.modulus;
        for (_, v) in &mut self.monomials {
            *v *= Integer::from(-1);
            *v %= &*self.modulus;
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
        self.constant %= &*self.modulus;
        for (_, v) in &mut self.monomials {
            *v *= other;
            *v %= &*self.modulus;
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
        self.constant %= &*self.modulus;
        for (_, v) in &mut self.monomials {
            *v *= Integer::from(other);
            *v %= &*self.modulus;
        }
    }
}

impl<S: Clone + Hash + Eq> R1cs<S> {
    pub fn new(modulus: Integer, values: bool) -> Self {
        R1cs {
            modulus: Rc::new(modulus),
            signal_idxs: HashMap::new(),
            idxs_signals: HashMap::new(),
            next_idx: 0,
            public_idxs: HashSet::new(),
            values: if values { Some(HashMap::new()) } else { None },
            constraints: Vec::new(),
        }
    }
    pub fn zero(&self) -> Lc {
        Lc {
            modulus: self.modulus.clone(),
            constant: Integer::from(0),
            monomials: HashMap::new(),
        }
    }
    pub fn signal_lc(&self, s: &S) -> Lc {
        let idx = self
            .signal_idxs
            .get(s)
            .expect("Missing signal in signal_lc");
        let mut lc = self.zero();
        lc.monomials.insert(*idx, Integer::from(1));
        lc
    }
    pub fn add_signal(&mut self, s: S) {
        self.signal_idxs.insert(s.clone(), self.next_idx);
        self.idxs_signals.insert(
            self.next_idx,
            std::iter::once(s.clone()).collect::<HashSet<_>>(),
        );
        self.next_idx += 1;
    }
    pub fn ensure_signal(&mut self, s: S) {
        if !self.signal_idxs.contains_key(&s) {
            self.add_signal(s)
        }
    }
    pub fn publicize(&mut self, s: &S) {
        self.signal_idxs
            .get(s)
            .cloned()
            .map(|i| self.public_idxs.insert(i));
    }
    pub fn constraint(&mut self, a: Lc, b: Lc, c: Lc) {
        assert_eq!(&self.modulus, &a.modulus);
        assert_eq!(&self.modulus, &b.modulus);
        assert_eq!(&self.modulus, &c.modulus);
        self.constraints.push((a, b, c));
    }
    pub fn set_value(&mut self, s: &S, v: Integer) {
        let idx = *self
            .signal_idxs
            .get(s)
            .expect("Missing signal in signal_lc");
        self.values.as_mut().expect("Missing values").insert(idx, v);
    }
}

pub struct Qeq(Lc, Lc, Lc);
