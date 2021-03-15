pub mod cfold;
pub mod flat;
pub mod mem;
pub mod sha;
pub mod inline;

use super::term::*;
use super::term::extras::Letified;
use log::debug;

#[derive(Debug)]
pub enum Opt {
    ConstantFold,
    Flatten,
    Sha,
    Mem,
    FlattenAssertions,
    Inline,
}

pub fn opt<I: IntoIterator<Item=Opt>>(mut cs: Constraints, optimizations: I) -> Constraints {
    //debug!("Initial: {}", Letified(cs.assertions_as_term()));
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
                let new_term =  flat::flatten_nary_ops(cs_term);
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
        //debug!("After {:?}: {}", i, Letified(cs.assertions_as_term()));
    }
    garbage_collect();
    cs
}
