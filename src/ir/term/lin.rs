//! Linearized terms.
//!
//! They can be serialized and evaluated more efficiently than normal terms

use super::*;
use std::convert::From;

#[derive(Serialize, Deserialize, Clone)]
/// A term represented as a sequence of operator applications (rather than with hash-consing).
///
pub struct LinTerm {
    steps: Vec<(Op, Vec<usize>)>,
}

impl From<&Term> for LinTerm {
    fn from(root: &Term) -> Self {
        let mut steps = Vec::new();
        let mut indices = TermMap::default();
        for (i, t) in PostOrderIter::new(root.clone()).enumerate() {
            let op = t.op().clone();
            let children = t
                .cs()
                .iter()
                .map(|c| *indices.get(c).unwrap())
                .collect::<Vec<_>>();
            indices.insert(t, i);
            steps.push((op, children))
        }
        Self { steps }
    }
}

impl From<LinTerm> for Term {
    fn from(lt: LinTerm) -> Self {
        let mut terms: Vec<Term> = Vec::new();
        for (o, children) in lt.steps {
            let term = term(o, children.iter().map(|i| terms[*i].clone()).collect());
            terms.push(term);
        }
        terms.pop().unwrap()
    }
}
