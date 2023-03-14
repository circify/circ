//! Keyed hashes

use crate::ir::term::{pf_lit, term, Op, Term, PF_ADD, PF_MUL};
use circ_fields::FieldT;

/// A multi-set hasher.
pub struct MsHasher {
    key: Term,
    f: FieldT,
}

impl MsHasher {
    /// Create a multi-set hasher for data uniquely determined by `inputs`.
    ///
    /// `key_name` must be unique.
    /// `f` is the field used.
    pub fn new(key_name: String, f: &FieldT, inputs: Vec<Term>) -> Self {
        Self {
            f: f.clone(),
            key: term(Op::PfChallenge(key_name, f.clone()), inputs),
        }
    }
    /// Hash some `data`, as a multi-set.
    pub fn hash(&self, data: Vec<Term>) -> Term {
        if data.is_empty() {
            pf_lit(self.f.new_v(1))
        } else {
            let ms_hash_shift = |input: Term| term![PF_ADD; input, self.key.clone()];
            term(PF_MUL, data.into_iter().map(ms_hash_shift).collect())
        }
    }
}

/// A multi-set hasher.
pub struct UniversalHasher {
    key_powers: Vec<Term>,
}

impl UniversalHasher {
    /// Create a multi-set hasher for data uniquely determined by `inputs`.
    ///
    /// * `key_name` must be unique.
    /// * `f` is the field used.
    /// * `len` is the data length.
    pub fn new(key_name: String, f: &FieldT, inputs: Vec<Term>, len: usize) -> Self {
        let key = term(Op::PfChallenge(key_name, f.clone()), inputs);
        let key_powers: Vec<Term> = std::iter::successors(Some(key.clone()), |p| {
            Some(term![PF_MUL; p.clone(), key.clone()])
        })
        .take(len - 1)
        .collect();
        Self { key_powers }
    }

    /// Hash some `data`, as a multi-set.
    pub fn hash(&self, data: Vec<Term>) -> Term {
        term(
            PF_ADD,
            data.into_iter()
                .enumerate()
                .map(|(i, d)| {
                    if i == 0 {
                        d
                    } else {
                        term![PF_MUL; d, self.key_powers[i-1].clone()]
                    }
                })
                .collect(),
        )
    }

    /// The data length of this hasher.
    pub fn len(&self) -> usize {
        self.key_powers.len() + 1
    }
}
