//! Optimizations
pub mod cfold;
pub mod flat;
pub mod inline;
pub mod mem;
pub mod sha;
pub mod tuple;

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
    /// Replace oblivious arrays with tuples
    Obliv,
    /// Replace arrays with linear scans
    LinearScan,
    /// Extract top-level ANDs as distinct outputs
    FlattenAssertions,
    /// Find outputs like `(= variable term)`, and substitute out `variable`
    Inline,
    /// Eliminate tuples
    Tuple,
}

/// Run optimizations on `cs`, in this order, returning the new constraint system.
pub fn opt<I: IntoIterator<Item = Opt>>(mut cs: Computation, optimizations: I) -> Computation {
    for i in optimizations {
        debug!("Applying: {:?}", i);
        match i {
            Opt::ConstantFold => {
                let mut cache = TermMap::new();
                for a in &mut cs.outputs {
                    *a = cfold::fold_cache(a, &mut cache);
                }
            }
            Opt::Sha => {
                for a in &mut cs.outputs {
                    *a = sha::sha_rewrites(a);
                }
            }
            Opt::Obliv => {
                mem::obliv::elim_obliv(&mut cs);
            }
            Opt::LinearScan => {
                for a in &mut cs.outputs {
                    *a = mem::lin::linearize(a, usize::MAX);
                }
            }
            Opt::FlattenAssertions => {
                let mut new_outputs = Vec::new();
                for a in std::mem::take(&mut cs.outputs) {
                    assert_eq!(check(&a), Sort::Bool, "Non-bool in {:?}", i);
                    if &a.op == &Op::BoolNaryOp(BoolNaryOp::And) {
                        new_outputs.extend(a.cs.iter().cloned());
                    } else {
                        new_outputs.push(a)
                    }
                }
                cs.outputs = new_outputs;
            }
            Opt::Flatten => {
                let mut cache = flat::Cache::new();
                for a in &mut cs.outputs {
                    *a = flat::flatten_nary_ops_cached(a.clone(), &mut cache);
                }
            }
            Opt::Inline => {
                let public_inputs = cs.metadata.public_inputs().map(ToOwned::to_owned).collect();
                inline::inline(&mut cs.outputs, &public_inputs);
            }
            Opt::Tuple => {
                cs = tuple::eliminate_tuples(cs);
            }
        }
        debug!("After {:?}: {} outputs", i, cs.outputs.len());
        //debug!("After {:?}: {}", i, Letified(cs.outputs[0].clone()));
        debug!("After {:?}: {} terms", i, cs.terms());
    }
    garbage_collect();
    cs
}
