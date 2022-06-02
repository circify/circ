//! Optimizations
pub mod binarize;
pub mod cfold;
pub mod flat;
pub mod inline;
pub mod link;
pub mod mem;
pub mod scalarize_vars;
pub mod sha;
pub mod tuple;
mod visit;

use std::{collections::HashMap, time::Instant};

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
pub fn opt<I: IntoIterator<Item = Opt>>(mut fs: Functions, optimizations: I) -> Functions {
    for i in optimizations {
        let mut opt_fs: Functions = fs.clone();
        for (name, comp) in fs.computations.iter_mut() {
            debug!("Applying: {:?}", i);
            println!("Applying: {:?} to {}", i, name);
            let now = Instant::now();
            match i.clone() {
                Opt::ScalarizeVars => scalarize_vars::scalarize_inputs(comp),
                Opt::ConstantFold(ignore) => {
                    // lock the collector because fold_cache locks TERMS
                    let _lock = super::term::COLLECT.read().unwrap();
                    let mut cache = TermCache::new(TERM_CACHE_LIMIT);
                    for a in &mut comp.outputs {
                        let n = Instant::now();
                        // allow unbounded size during a single fold_cache call
                        cache.resize(std::usize::MAX);
                        *a = cfold::fold_cache(a, &mut cache, &*ignore.clone());
                        // then shrink back down to size between calls
                        cache.resize(TERM_CACHE_LIMIT);
                        println!("{:#?}", n.elapsed());
                    }
                    println!("cache size per term: {}", cache.len());
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
                    let mut cache = link::Cache::new();
                    for a in &mut comp.outputs {
                        *a = link::link_function_calls(a.clone(), &mut cache, &opt_fs);
                    }
                }
                Opt::Tuple => {
                    tuple::eliminate_tuples(comp);
                }
            }
            debug!("{:?} took {:#?}.\n", i, now.elapsed());
            debug!("After {:?}: {} outputs", i, comp.outputs.len());
            //debug!("After {:?}: {}", i, Letified(cs.outputs[0].clone()));
            debug!("After {:?}: {} terms", i, comp.terms());
            // for t in comp.terms_postorder() {
            //     println!("post t, ty: {}\n{}\n{}\n", t, check(&t), check_rec(&t));
            // }

            opt_fs.insert(name.clone(), comp.clone());
        }
        fs = opt_fs;
    }
    garbage_collect();
    fs
}
