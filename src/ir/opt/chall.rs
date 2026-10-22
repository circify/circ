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
use log::{debug, trace};

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::ir::opt::visit::RewritePass;
use crate::ir::proof::PROVER_ID;
use crate::ir::term::*;
use crate::util::ns::Uniquer;
use circ_fields::FieldT;

/// Replace witness terms with new variables.
pub fn deskolemize_witnesses(comp: &mut Computation) {
    // skip pass if no witnesses
    if !comp
        .terms_postorder()
        .any(|t| matches!(t.op(), Op::Witness(..)))
    {
        return;
    }

    struct WitPass(Uniquer);

    impl RewritePass for WitPass {
        fn visit<F: Fn() -> Vec<Term>>(
            &mut self,
            computation: &mut Computation,
            orig: &Term,
            _rewritten_children: F,
        ) -> Option<Term> {
            if let Op::Witness(prefix) = orig.op() {
                let name = self.0.mk_uniq(prefix);
                let sort = check(orig);
                let var =
                    computation.new_var(&name, sort, Some(PROVER_ID), Some(orig.cs()[0].clone()));
                Some(var)
            } else {
                None
            }
        }
    }

    let names_iterator = comp
        .terms_postorder()
        .filter(|t| t.is_var())
        .map(|t| t.as_var_name().to_string())
        .chain(comp.precomputes.outputs().iter().map(|o| o.0.clone()))
        .chain(comp.precomputes.inputs().iter().map(|o| o.0.clone()));
    let uniqer = Uniquer::new(names_iterator);
    WitPass(uniqer).traverse_full(comp, true, true);
}

/// Resolve challenges that share a name.
///
/// A transform declares that two coins may be the same by giving them the same
/// name; this pass decides what to do about it. With `share`, same-named
/// challenges of the same field become one coin, drawn after everything any of
/// them depended on (its children are the union of theirs). Without it, they are
/// renamed apart, so each is its own coin.
///
/// Either way the pass restores the invariant [deskolemize_challenges] needs --
/// distinct challenge terms have distinct names -- which is otherwise only a
/// `debug_assert` in [ComputationMetadata::new_input_from_meta]: in release, two
/// same-named challenges silently become one variable, keeping whichever
/// metadata was written last. So this runs whether or not sharing is on.
///
/// The independence information a merge has to respect is already in the IR: a
/// challenge's arguments are what it is sampled independently of ([Op::PfChallenge]),
/// so a coin with another coin among its dependents must not be identified with
/// it. This pass takes the conservative version of that test and never merges a
/// challenge that has a challenge below it at all -- doing so would union in a
/// child that mentions a challenge, which can build a cycle. Such a challenge
/// still gets a name of its own if merging leaves its old one taken; it just
/// never joins a merge. The coins a transform wants to share are drawn from
/// witnesses, not from other coins, so this costs nothing in practice.
///
/// What the *name* adds is the grouping: which coins a transform is willing to
/// identify. That claim cannot be read off the dependents, because two coins can
/// have identical dependents and still need to differ -- the RAM checker's
/// `uhf_key` and `ms_hash_key` are built over the same inputs, and sharing them
/// would collapse the compression randomness into the multiset evaluation point.
/// Sharing is therefore opt-in: a transform asks for it by naming coins alike.
pub fn share_challenges(comp: &mut Computation, share: bool) {
    // Every challenge with this (name, field), whether or not it is eligible to
    // merge -- a name collision among these has to be resolved either way.
    let mut groups: BTreeMap<(Box<str>, FieldT), Vec<Term>> = BTreeMap::new();
    // A challenge with another challenge below it cannot be merged; see above.
    let mut chall_below: TermMap<bool> = TermMap::default();
    for t in comp.terms_postorder() {
        let below = t
            .cs()
            .iter()
            .any(|c| matches!(c.op(), Op::PfChallenge(..)) || chall_below[c]);
        if let Op::PfChallenge(c) = t.op() {
            groups
                .entry((c.name.clone(), c.field.clone()))
                .or_default()
                .push(t.clone());
        }
        chall_below.insert(t, below);
    }

    // The name each challenge term ends up with, and the merged children of the
    // groups that are being shared.
    let mut names: TermMap<String> = TermMap::default();
    let mut merged: TermMap<Vec<Term>> = TermMap::default();
    let mut uniquer = Uniquer::new(
        comp.terms_postorder()
            .filter_map(|t| match t.op() {
                Op::PfChallenge(c) => Some(c.name.to_string()),
                _ => None,
            })
            .chain(comp.metadata.ordered_input_names()),
    );
    for ((name, _field), mut members) in groups {
        if members.len() < 2 {
            continue;
        }
        // Stable across runs, so the merged term is too.
        members.sort_by_key(|t| t.id());
        let (eligible, ineligible): (Vec<Term>, Vec<Term>) =
            members.into_iter().partition(|m| !chall_below[m]);
        if share && eligible.len() >= 2 {
            let mut children: Vec<Term> = Vec::new();
            let mut seen = TermSet::default();
            for m in &eligible {
                for c in m.cs() {
                    if seen.insert(c.clone()) {
                        children.push(c.clone());
                    }
                }
            }
            debug!(
                "sharing {} challenges named {} over {} inputs",
                eligible.len(),
                name,
                children.len()
            );
            for m in eligible {
                names.insert(m.clone(), name.to_string());
                merged.insert(m, children.clone());
            }
            // These share the name but could not join the merge: they still
            // need a name of their own.
            for m in ineligible {
                names.insert(m, uniquer.mk_uniq(&name));
            }
        } else {
            // Nothing in this group merges (sharing is off, or fewer than two
            // members qualify): keep one member's name, rename everyone else in
            // the group apart, eligible or not.
            for m in eligible.into_iter().chain(ineligible).skip(1) {
                names.insert(m, uniquer.mk_uniq(&name));
            }
        }
    }
    if names.is_empty() {
        return;
    }
    SharePass { names, merged }.traverse_full(comp, true, true);
}

struct SharePass {
    names: TermMap<String>,
    merged: TermMap<Vec<Term>>,
}

impl RewritePass for SharePass {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        let Op::PfChallenge(c) = orig.op() else {
            return None;
        };
        let name = self.names.get(orig)?;
        // A merged group's children contain no challenges, so they need no
        // rewriting; a renamed challenge keeps its own (rewritten) children.
        let children = self
            .merged
            .get(orig)
            .cloned()
            .unwrap_or_else(rewritten_children);
        Some(term(Op::new_chall(name.clone(), c.field.clone()), children))
    }
}

/// Replace the challenge terms in this computation with random inputs.
pub fn deskolemize_challenges(comp: &mut Computation) {
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
            Op::Var(v) => {
                if let Some(v) = comp.precomputes.outputs().get(&*v.name) {
                    *min_round
                        .borrow()
                        .get(v)
                        .unwrap_or_else(|| panic!("missing key: {}", v))
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
            Op::Var(v) if comp.metadata.is_input_public(&v.name) => 0,
            Op::Var(v) if comp.metadata.lookup(&*v.name).committed => 0,
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
        if let Op::PfChallenge(c) = t.op() {
            let round = *actual_round.get(&t).unwrap();
            debug!("challenge {}: round = {round}", c.name);
            trace!("challenge term {t}");
            let md = VariableMetadata {
                name: c.name.to_string(),
                random: true,
                vis: None,
                sort: Sort::Field(c.field.clone()),
                round,
                ..Default::default()
            };
            let var = comp.new_var_metadata(md, None);
            challs.insert(t, var);
        }
    }
    debug!("{} challenge(s) skolemized", challs.len());
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
            Some(
                self.0
                    .get(orig)
                    .unwrap_or_else(|| panic!("missing key: {}", orig))
                    .clone(),
            )
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use circ_fields::FieldT;

    /// Two same-named challenges over disjoint dependents: `share` merges them
    /// into one variable whose dependents are the union; without it, they are
    /// renamed apart into two variables.
    #[test]
    fn share_merges_same_named_challenges() {
        env_logger::try_init().ok();
        let src = b"
            (computation
                (metadata
                    (parties P)
                    (inputs (x (mod 11) (party 0)) (y (mod 11) (party 0)))
                    (commitments)
                )
                (precompute () () (#t ))
                (=
                    (= (* ((challenge same 11) x) x) #f1m11)
                    (= (* ((challenge same 11) y) y) #f1m11)
                )
            )
            ";
        for share in [false, true] {
            let mut cs = text::parse_computation(src);
            share_challenges(&mut cs, share);
            let names: Vec<String> = cs
                .terms_postorder()
                .filter_map(|t| match t.op() {
                    Op::PfChallenge(c) => Some(c.name.to_string()),
                    _ => None,
                })
                .collect();
            if share {
                // one term left, and its children cover both x and y
                assert_eq!(names, vec!["same".to_string()]);
                let chall = cs
                    .terms_postorder()
                    .find(|t| matches!(t.op(), Op::PfChallenge(..)))
                    .unwrap();
                assert_eq!(chall.cs().len(), 2, "expected the union of dependents");
            } else {
                // two terms, renamed apart
                assert_eq!(names.len(), 2);
                assert_ne!(names[0], names[1]);
            }
            // Distinct challenge names never collide as variables.
            deskolemize_challenges(&mut cs);
        }
    }

    /// A challenge with another challenge among its dependents refuses to merge
    /// with same-named challenges, even when asked to share: doing so would
    /// union in a child that is itself a challenge, which can create a cycle.
    #[test]
    fn share_refuses_challenges_below_challenges() {
        env_logger::try_init().ok();
        let src = "
            (computation
                (metadata
                    (parties P)
                    (inputs (x (mod 11) (party 0)))
                    (commitments)
                )
                (precompute () () (#t ))
                (=
                    (= (* ((challenge same 11) x) x) #f1m11)
                    (= (* ((challenge same 11) ((challenge other 11) x)) x) #f1m11)
                )
            )
            ";
        let mut cs = text::parse_computation(src.as_bytes());
        share_challenges(&mut cs, true);
        let names: Vec<String> = cs
            .terms_postorder()
            .filter_map(|t| match t.op() {
                Op::PfChallenge(c) => Some(c.name.to_string()),
                _ => None,
            })
            .collect();
        // three challenges (same, same, other), and the two `same`s were
        // renamed apart rather than merged, since one sits below the other.
        assert_eq!(names.len(), 3);
        let same_count = names.iter().filter(|n| n.starts_with("same")).count();
        assert_eq!(same_count, 2);
        assert_ne!(
            names
                .iter()
                .filter(|n| n.starts_with("same"))
                .collect::<Vec<_>>()[0],
            names
                .iter()
                .filter(|n| n.starts_with("same"))
                .collect::<Vec<_>>()[1]
        );
        deskolemize_challenges(&mut cs);
    }

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
        deskolemize_challenges(&mut cs);
        println!("{}", text::serialize_computation(&cs));
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
    }
}
