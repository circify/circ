//! Optimizations
pub mod binarize;
pub mod cfold;
pub mod flat;
pub mod inline;
pub mod inline_calls;
pub mod mem;
pub mod scalarize_vars;
pub mod sha;
pub mod tuple;
mod visit;

use super::term::*;
use log::debug;

#[derive(Clone, Debug)]
/// An optimization pass
pub enum Opt {
    /// Convert non-scalar (tuple, array) inputs to scalar ones
    /// The scalar variable names are suffixed with .N, where N indicates the array/tuple position
    ScalarizeVars,
    /// Fold constants
    ConstantFold(Box<[Op]>),
    /// Flatten n-ary operators
    Flatten,
    /// Binarize n-ary operators
    Binarize,
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
    /// Inline function calls
    InlineCalls,
    /// Eliminate tuples
    Tuple,
}

/// Run optimizations on `cs`, in this order, returning the new constraint system.
pub fn opt<I: IntoIterator<Item = Opt>>(mut cs: Computations, optimizations: I) -> Computations {
    for i in optimizations {
        let mut opt_cs: Computations = cs.clone();
        for (fd, comp) in cs.functions.iter_mut() {
            debug!("Applying: {:?}", i);
            match i.clone() {
                Opt::ScalarizeVars => scalarize_vars::scalarize_inputs(comp),
                Opt::ConstantFold(ignore) => {
                    // lock the collector because fold_cache locks TERMS
                    let _lock = super::term::COLLECT.read().unwrap();

                    let mut cache = TermCache::new(TERM_CACHE_LIMIT);
                    for a in &mut comp.outputs {
                        // allow unbounded size during a single fold_cache call
                        cache.resize(std::usize::MAX);
                        *a = cfold::fold_cache(a, &mut cache, &*ignore.clone());
                        // then shrink back down to size between calls
                        cache.resize(TERM_CACHE_LIMIT);
                    }
                }
                Opt::Sha => {
                    for a in &mut comp.outputs {
                        *a = sha::sha_rewrites(a);
                    }
                }
                Opt::Obliv => {
                    mem::obliv::elim_obliv(comp);
                }
                Opt::LinearScan => {
                    mem::lin::linearize(comp);
                }
                Opt::FlattenAssertions => {
                    let mut new_outputs = Vec::new();
                    for a in std::mem::take(&mut comp.outputs) {
                        assert_eq!(check(&a), Sort::Bool, "Non-bool in {:?}", i);
                        if a.op == Op::BoolNaryOp(BoolNaryOp::And) {
                            new_outputs.extend(a.cs.iter().cloned());
                        } else {
                            new_outputs.push(a)
                        }
                    }
                    comp.outputs = new_outputs;
                }
                Opt::Flatten => {
                    let mut cache = flat::Cache::new();
                    for a in &mut comp.outputs {
                        *a = flat::flatten_nary_ops_cached(a.clone(), &mut cache);
                    }
                }
                Opt::Binarize => {
                    let mut cache = binarize::Cache::new();
                    for a in &mut comp.outputs {
                        *a = binarize::binarize_nary_ops_cached(a.clone(), &mut cache);
                    }
                }
                Opt::Inline => {
                    let public_inputs = comp
                        .metadata
                        .public_input_names()
                        .map(ToOwned::to_owned)
                        .collect();
                    inline::inline(&mut comp.outputs, &public_inputs);
                }
                Opt::InlineCalls => {
                    let mut cache = inline_calls::Cache::new();
                    for a in &mut comp.outputs {
                        *a = inline_calls::inline_function_calls(a.clone(), &mut cache, &opt_cs);
                    }
                }
                Opt::Tuple => {
                    tuple::eliminate_tuples(comp);
                }
            }
            debug!("After {:?}: {} outputs", i, comp.outputs.len());
            //debug!("After {:?}: {}", i, Letified(cs.outputs[0].clone()));
            debug!("After {:?}: {} terms", i, comp.terms());
            opt_cs.insert_comp(fd.clone(), comp.clone());
        }
        cs = opt_cs;
    }
    garbage_collect();
    cs
}
