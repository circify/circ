//! Optimizations
pub mod cfold;
pub mod flat;
pub mod inline;
pub mod mem;
pub mod sha;

use super::term::*;
use log::debug;

#[derive(Debug)]
/// An optimization pass
pub enum Opt {
    /// Fold constants
    ConstantFold,
    /// Flatten n-ary operators
    Flatten,
    /// SHA-2 peephole optimizations
    Sha,
    /// Memory elimination
    Mem,
    /// Extract top-level ANDs as distinct assertions
    FlattenAssertions,
    /// Find assertions like `(= variable term)`, and substitute out `variable`
    Inline,
}

/// Run optimizations on `cs`, in this order, returning the new constraint system.
pub fn opt<I: IntoIterator<Item = Opt>>(mut cs: Constraints, optimizations: I) -> Constraints {
    for i in optimizations {
        debug!("Applying: {:?}", i);
        match i {
            Opt::ConstantFold => {
                let mut cache = TermMap::new();
                for a in &mut cs.assertions {
                    *a = cfold::fold_cache(a, &mut cache);
                }
            }
            Opt::Sha => {
                for a in &mut cs.assertions {
                    *a = sha::sha_rewrites(a);
                }
            }
            Opt::Mem => {
                for a in &mut cs.assertions {
                    *a = mem::array_elim(a);
                }
            }
            Opt::FlattenAssertions => {
                let mut new_assertions = Vec::new();
                for a in std::mem::take(&mut cs.assertions) {
                    if &a.op == &Op::BoolNaryOp(BoolNaryOp::And) {
                        new_assertions.extend(a.cs.iter().cloned());
                    } else {
                        new_assertions.push(a)
                    }
                }
                cs.assertions = new_assertions;
            }
            Opt::Flatten => {
                let cs_term = cs.assertions_as_term();
                let new_term = flat::flatten_nary_ops(cs_term);
                let assertions = if new_term.op == Op::BoolNaryOp(BoolNaryOp::And) {
                    new_term.cs.clone()
                } else {
                    vec![new_term]
                };
                cs.assertions = assertions;
            }
            Opt::Inline => {
                inline::inline(&mut cs.assertions, &cs.public_inputs);
            }
        }
        debug!("After {:?}: {}", i, cs.terms());
    }
    garbage_collect();
    cs
}
