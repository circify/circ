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
    debug!("Initial: {}", Letified(cs.assertions_as_term()));
    for i in optimizations {
        match i {
            Opt::ConstantFold => {
                for a in &mut cs.assertions {
                    *a = cfold::fold(a);
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
                for a in &mut cs.assertions {
                    *a = flat::flatten_nary_ops(a.clone());
                }
            }
            Opt::Inline => {
                inline::inline(&mut cs.assertions, &cs.public_inputs);
            }
        }
        debug!("After {:?}: {}", i, Letified(cs.assertions_as_term()));
    }
    cs
}
