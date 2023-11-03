//! Optimizations
pub mod binarize;
pub mod cfold;
pub mod chall;
pub mod cstore;
pub mod flat;
pub mod inline;
pub mod link;
pub mod mem;
pub mod scalarize_vars;
pub mod sha;
pub mod tuple;
mod visit;

use super::term::*;

use log::{debug, trace};

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
    /// Find conditional stores.
    ParseCondStores,
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
    /// Link function calls
    Link,
    /// Eliminate persistent RAM
    PersistentRam,
    /// Eliminate volatile RAM
    VolatileRam,
    /// Replace challenge terms with random variables
    SkolemizeChallenges,
}

/// Run optimizations on `cs`, in this order, returning the new constraint system.
pub fn opt<I: IntoIterator<Item = Opt>>(mut cs: Computations, optimizations: I) -> Computations {
    for i in optimizations {
        debug!("Applying: {:?}", i);

        if let Opt::Link = i {
            link::link_all_function_calls(&mut cs);
            continue;
        }

        for (_, c) in cs.comps.iter_mut() {
            match i.clone() {
                Opt::ParseCondStores => {
                    cstore::parse(c);
                }
                Opt::ScalarizeVars => {
                    scalarize_vars::scalarize_inputs(c);
                }
                Opt::ConstantFold(ignore) => {
                    let mut cache = TermCache::with_capacity(TERM_CACHE_LIMIT);
                    cache.resize(std::usize::MAX);
                    for a in &mut c.outputs {
                        *a = cfold::fold_cache(a, &mut cache, &ignore.clone());
                    }
                    c.ram_arrays = c
                        .ram_arrays
                        .iter()
                        .map(|a| cfold::fold_cache(a, &mut cache, &ignore.clone()))
                        .collect();
                }
                Opt::Sha => {
                    for a in &mut c.outputs {
                        *a = sha::sha_rewrites(a);
                    }
                }
                Opt::Obliv => {
                    mem::obliv::elim_obliv(c);
                }
                Opt::LinearScan => {
                    mem::lin::linearize(c);
                }
                Opt::FlattenAssertions => {
                    let mut new_outputs = Vec::new();
                    for a in std::mem::take(&mut c.outputs) {
                        assert_eq!(check(&a), Sort::Bool, "Non-bool in {i:?}");
                        if a.op() == &Op::BoolNaryOp(BoolNaryOp::And) {
                            new_outputs.extend(a.cs().iter().cloned());
                        } else {
                            new_outputs.push(a)
                        }
                    }
                    c.outputs = new_outputs;
                }
                Opt::Flatten => {
                    let mut cache = flat::Cache::new();
                    for a in &mut c.outputs {
                        *a = flat::flatten_nary_ops_cached(a.clone(), &mut cache);
                    }
                }
                Opt::Binarize => {
                    let mut cache = binarize::Cache::new();
                    for a in &mut c.outputs {
                        *a = binarize::binarize_nary_ops_cached(a.clone(), &mut cache);
                    }
                }
                Opt::Inline => {
                    let public_inputs = c.metadata.public_input_names_set();
                    inline::inline(&mut c.outputs, &public_inputs);
                }
                Opt::Tuple => {
                    tuple::eliminate_tuples(c);
                }
                Opt::Link => unreachable!(),
                Opt::PersistentRam => {
                    let cfg = mem::ram::AccessCfg::from_cfg();
                    mem::ram::persistent::apply(c, &cfg);
                }
                Opt::VolatileRam => {
                    let cfg = mem::ram::AccessCfg::from_cfg();
                    mem::ram::volatile::apply(c, &cfg);
                }
                Opt::SkolemizeChallenges => {
                    chall::skolemize_challenges(c);
                }
            }
            debug!("After {:?}: {} outputs", i, c.outputs.len());
            trace!("After {:?}: {}", i, c.outputs[0]);
            //debug!("After {:?}: {}", i, Letified(cs.outputs[0].clone()));
            debug!("After {:?}: {} terms", i, c.terms());
        }
        if crate::cfg::cfg().ir.frequent_gc {
            garbage_collect();
        }
    }
    if !crate::cfg::cfg().ir.frequent_gc {
        garbage_collect();
    }
    cs
}
