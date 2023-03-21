//! Eliminate challenge operators by skolemizing them as random inputs.
//!
//! First, we compute, for very term or precompute term t, the minimal round at which t's value is
//! known: min_round(t). Rules:
//!
//! * for var v w/ precompute p: min_round(v) = min_round(p)
//! * for challenge c: min_round(c) = 1 + max(min_round(d) for children d of c, 0)
//! * for any other term t: min_round(t) = max(min_round(d) for children d of c, 0)
//!
//! Now, for each each challenge c, we define round(c) = min_round(c) - 1. c will be
//! skolemized as a round(c)-round variable.
//!
//! We still need to set the rounds of other variables. The rule is that if c depends on variable
//! v, then round(v) < round(c). Subject to that, we want to maximize variable rounds.
//! So, we do a parents-to-children pass.
//!
//! For a variable v: min_round(v) = max(min_round
//!
//! Each challenge term c that depends on t is replaced with a variable v.
//! Let t' denote a rewritten term.
//!
//! Rules:
//! * round(v) >=
//! round(v
use log::{debug, trace};

use std::cell::RefCell;
use std::collections::BTreeSet;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

/// Replace the challenge terms in this computation with random inputs.
pub fn skolemize_challenges(comp: &mut Computation) {
    for var in comp.metadata.ordered_input_names() {
        let md = comp.metadata.lookup(&var);
        assert_eq!(md.round, 0, "There are already rounds");
        assert!(!md.random, "There are already random variables");
    }
    let any_challenges = comp
        .terms_postorder()
        .any(|t| matches!(t.op(), Op::PfChallenge(..)));
    if !any_challenges {
        return;
    }

    // This term cannot be known until after this many challenges.
    // A challenge's min_round is 1 more than its children.
    let min_round: RefCell<TermMap<u8>> = Default::default();

    // we have to post-order traverse the precompute, and then the main computation
    let set_round = |t: Term| {
        let children_max = t
            .cs()
            .iter()
            .map(|child| *min_round.borrow().get(child).unwrap())
            .max()
            .unwrap_or(0);
        let round = match t.op() {
            Op::Var(n, _) => {
                if let Some(v) = comp.precomputes.outputs().get(n) {
                    *min_round.borrow().get(v).unwrap()
                } else {
                    0
                }
            }
            Op::PfChallenge(..) => children_max.checked_add(1).unwrap(),
            _ => children_max,
        };
        min_round.borrow_mut().insert(t, round);
    };
    for (name, _sort) in comp.precomputes.sequence() {
        let value = comp.precomputes.outputs().get(name).unwrap().clone();
        for t in
            extras::PostOrderSkipIter::new(value.clone(), &|t| min_round.borrow().contains_key(t))
        {
            set_round(t);
        }
    }
    for t in comp.terms_postorder() {
        set_round(t);
    }

    let parents = extras::parents_map(comp);
    let min_round = min_round.into_inner();
    for t in comp.terms_postorder() {
        if t.is_var() || matches!(t.op(), Op::PfChallenge(..)) {
            let child_ids: Vec<_> = t.cs().iter().map(|c| c.id()).collect();
            trace!(
                "Term {} ({} {:?}): min_round = {}",
                t.id(),
                t.op(),
                child_ids,
                min_round.get(&t).unwrap(),
            );
        }
    }

    let final_round = min_round.values().max().cloned().unwrap_or(1);
    // This term must be fixed before this many challenges.
    let mut actual_round: TermMap<u8> = Default::default();
    let terms: Vec<Term> = comp.terms_postorder().collect();
    for t in terms.into_iter().rev() {
        let round = match t.op() {
            Op::PfChallenge(..) => min_round.get(&t).unwrap().checked_sub(1).unwrap(),
            Op::Var(name, _) if comp.metadata.is_input_public(name) => 0,
            Op::Var(name, _) if comp.metadata.lookup(name).committed => 0,
            _ => parents
                .get(&t)
                .unwrap()
                .iter()
                .map(|p| *actual_round.get(p).unwrap())
                .min()
                .unwrap_or(final_round),
        };
        actual_round.insert(t, round);
    }
    for t in comp.terms_postorder() {
        if t.is_var() || matches!(t.op(), Op::PfChallenge(..)) {
            let child_ids: Vec<_> = t.cs().iter().map(|c| c.id()).collect();
            trace!(
                "Term {} ({} {:?}): round = {}",
                t.id(),
                t.op(),
                child_ids,
                actual_round.get(&t).unwrap(),
            );
        }
    }
    for name in comp.metadata.ordered_input_names() {
        let md = comp.metadata.lookup_mut(&name);
        md.round = *actual_round.get(&md.term()).unwrap_or(&0);
    }

    let mut challs = TermMap::default();
    for t in comp.terms_postorder() {
        if let Op::PfChallenge(name, field) = t.op() {
            let md = VariableMetadata {
                name: name.clone(),
                random: true,
                vis: None,
                sort: Sort::Field(field.clone()),
                round: *actual_round.get(&t).unwrap(),
                ..Default::default()
            };
            let var = comp.new_var_metadata(md, None);
            challs.insert(t, var);
        }
    }
    compact_rounds(&mut comp.metadata);

    Pass(challs).traverse_full(comp, true, false);
}

/// Eliminate empty rounds, if there are any.
fn compact_rounds(c: &mut ComputationMetadata) {
    let mut max_round = 0;
    let used_rounds: BTreeSet<u8> = c
        .ordered_input_names()
        .into_iter()
        .filter_map(|n| {
            let md = c.lookup(&n);
            max_round = max_round.max(md.round);
            (!md.random).then_some(md.round)
        })
        .collect();
    if max_round + 1 > used_rounds.len() as u8 {
        debug!("Running round compaction");
        let mut round_map: Vec<u8> = Vec::new();
        let mut new_round = 0u8.wrapping_sub(1);
        for orig_round in 0..=max_round {
            if used_rounds.contains(&orig_round) {
                new_round = new_round.wrapping_add(1);
            }
            round_map.push(new_round);
        }

        // check that output rounds are contiguous and <= original rounds
        assert_eq!(round_map.len() as u8, max_round + 1);
        for i in 0..round_map.len() {
            if i != 0 {
                assert!(round_map[i] <= round_map[i - 1] + 1);
            }
            assert!(round_map[i] <= i as u8);
        }

        for v in c.ordered_input_names() {
            let md = c.lookup_mut(&v);
            let new_round = round_map[md.round as usize];
            trace!("Changing {} from round {} to {}", v, md.round, new_round);
            md.round = new_round;
        }
    } else {
        debug!("Skipping round compaction");
    }
}

struct Pass(TermMap<Term>);

impl RewritePass for Pass {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        _rewritten_children: F,
    ) -> Option<Term> {
        if let Op::PfChallenge(..) = orig.op() {
            Some(self.0.get(orig).unwrap().clone())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use circ_fields::FieldT;

    #[test]
    fn length_4() {
        env_logger::try_init().ok();
        let mut cs = text::parse_computation(
            b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (A (array (mod 11) (mod 11) 4) (committed))
                        (x (mod 11) (party 0))
                        (return (mod 11))
                    )
                    ; (commitments (commitment A))
                    (commitments)
                )
                (precompute () () (#t ))
                (persistent_arrays (A 4 (store A x #f0m11)))
                (= return (select A x))
            )
        ",
        );
        let values = text::parse_value_map(
            b"
            (set_default_modulus 11
            (let (
                (A (#l (mod 11) (#f1 #f2 #f3 #f4)))
                (x #f0)
                (return #f1)
            ) false ; ignored
            ))
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
        let field = FieldT::from(rug::Integer::from(11));
        let cfg = super::super::mem::ram::AccessCfg::default_from_field(field);
        super::super::mem::ram::persistent::apply(&mut cs, &cfg);
        println!("{}", text::serialize_computation(&cs));
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
        skolemize_challenges(&mut cs);
        println!("{}", text::serialize_computation(&cs));
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
    }
}
