//! Substitutions

use super::cfold;
use crate::ir::term::extras::*;
use crate::ir::term::*;
use fxhash::FxHashSet;

/// This is a tool for sweeping a list of equations, some of which define new variables as
/// functions of previous ones, and eliminating these new variables, by substituting them
/// elsewhere.
///
///
pub struct Inliner<'a> {
    /// Map from variables to their values.
    /// Invariant: no key variable in in any value variable.
    /// Invariant: one a key appears in this map, it is never removed.
    substs: TermMap<Term>,
    /// The substitution cache.
    /// Must be reinitialized when `substs` are updated.
    /// Invariant: no key variable from `substs` is in any value of the cache.
    subst_cache: TermMap<Term>,

    /// A set of variables which are *not* new.
    /// Invariant: contains all variables from substs.
    stale_vars: TermSet,

    /// Variables that are "protected": they should not be eliminated.
    protected: &'a FxHashSet<String>,
}

impl<'a> Inliner<'a> {
    fn new(protected: &'a FxHashSet<String>) -> Self {
        Self {
            substs: TermMap::default(),
            subst_cache: TermMap::default(),
            stale_vars: TermSet::default(),
            protected,
        }
    }

    /// Checks invariant that no key variable is in any `substs` value.
    /// Also checks that no key variable is in any `subst_cache` value.
    #[allow(dead_code)]
    fn check_substs(&self) {
        let keys: FxHashSet<&Term> = self.substs.keys().collect();
        for (key, value) in &self.substs {
            for child in PostOrderIter::new(value.clone()) {
                assert!(
                    !keys.contains(&child),
                    "{}",
                    "Substituted variable {child} is in the substitution for {key}, {value}"
                );
                if child.is_var() {
                    assert!(
                        self.stale_vars.contains(&child),
                        "{}",
                        "Variable {child} in the substitution for {key}, {value} is not marked stale"
                    );
                }
            }
            assert!(
                self.stale_vars.contains(key),
                "{}",
                "Variable {key}, which is being susbstituted",
            );
        }
        for (key, value) in &self.subst_cache {
            for child in PostOrderIter::new(value.clone()) {
                assert!(
                    !keys.contains(&child),
                    "{}",
                    format!("Substituted variable {child} is in the cache for {key}, {value}"),
                );
                if child.is_var() {
                    assert!(
                        self.stale_vars.contains(&child),
                        "{}",
                        format!("Variable {child} in the substitution cache for {key}, {value} is not marked stale")
                    );
                }
            }
        }
    }

    /// Applies the current substitutions to `t`.
    fn apply(&mut self, t: &Term) -> Term {
        cfold::fold(&substitute_cache(t, &mut self.subst_cache), &[])
    }

    /// Syntactically analyzes `t`, seeing if it has form
    ///
    ///    * `(= v t')` OR
    ///    * `(= t' v)`
    ///
    /// where `v` is a fresh variable and is not in `t'`.
    ///
    /// If such a condition is met, returns `(v, t')`.
    /// Prefers the first form, if both match.
    ///
    /// Will not return `v` which are protected.
    fn as_fresh_def(&self, t: &Term) -> Option<(Term, Term)> {
        if &EQ == t.op() {
            if let Op::Var(name, _) = &t.cs()[0].op() {
                if !self.stale_vars.contains(&t.cs()[0])
                    && !self.protected.contains(name)
                    && does_not_contain(t.cs()[1].clone(), &t.cs()[0])
                {
                    return Some((t.cs()[0].clone(), t.cs()[1].clone()));
                }
            }
            if let Op::Var(name, _) = &t.cs()[1].op() {
                if !self.stale_vars.contains(&t.cs()[1])
                    && !self.protected.contains(name)
                    && does_not_contain(t.cs()[0].clone(), &t.cs()[1])
                {
                    return Some((t.cs()[1].clone(), t.cs()[0].clone()));
                }
            }
        }
        None
    }

    /// Examines term, applying the stored substitutions to it, and internalizing it as a
    /// substitution if possible.
    ///
    /// If `t` is not a substitution, then its (substituted variant) is returned.
    fn ingest_term(&mut self, t: &Term) -> Option<Term> {
        if let Some((var, val)) = self.as_fresh_def(t) {
            //debug!(target: "circ::ir::opt::inline", "Inline: {} -> {}", var, val.clone());
            // Rewrite the substitution
            let subst_val = self.apply(&val);

            // Add it to the sub list and sub cache.
            self.substs.insert(var.clone(), subst_val.clone());
            // We need not fully refresh the cache because the sub we're adding is fresh.
            self.subst_cache.insert(var.clone(), subst_val);

            // Mark the original variables as stale.
            // We need not mark the rewritten ones, because all variables in rewrites are already
            // marked stale.
            self.stale_vars.insert(var);
            self.stale_vars
                .extend(PostOrderIter::new(val).filter(|t| t.is_var()));

            // Comment out?
            //self.check_substs();

            None
        } else {
            self.stale_vars
                .extend(PostOrderIter::new(t.clone()).filter(|t| t.is_var()));
            let subst_t = self.apply(t);
            Some(subst_t)
        }
    }
}

/// Performs "inline" optimizations.
///
/// That is, finds equalities between variables and terms, and substitutes the term for the
/// variable.
///
/// Maintains a few invariants as it sweeps the assertions.
///
/// First, maintains a set of variables being substituted.
/// Second, maintain a
pub fn inline(assertions: &mut Vec<Term>, public_inputs: &FxHashSet<String>) {
    let mut new_assertions = Vec::new();
    let mut inliner = Inliner::new(public_inputs);
    for assertion in assertions.drain(..) {
        if let Some(rewritten_assertion) = inliner.ingest_term(&assertion) {
            new_assertions.push(rewritten_assertion);
        }
    }
    *assertions = new_assertions;
}

#[cfg(all(feature = "smt", feature = "test"))]
mod test {
    use super::*;
    use crate::target::smt::{check_sat, find_model};

    fn b_var(b: &str) -> Term {
        leaf_term(Op::Var(b.to_string(), Sort::Bool))
    }

    fn sub_test(xs: Vec<Term>, n: usize) {
        let mut ys = xs.clone();
        let p = FxHashSet::default();
        inline(&mut ys, &p);
        assert_eq!(n, ys.len());
        let x = term(AND, xs.clone());
        let y = term(AND, ys.clone());
        let imp = term![IMPLIES; x.clone(), y.clone()];
        let not_imp = term![NOT; imp];
        if let Some(cex) = find_model(&not_imp) {
            println!("Inputs:");
            for x_i in xs {
                println!("  {}", x_i);
            }
            println!("Inlined:");
            for x_i in ys {
                println!("  {}", x_i);
            }
            println!("Counterexample to inputs->outputs:");
            for (n, v) in &cex {
                println!("  {} -> {}", n, v);
            }
            panic!("Invalid inline");
        }
        let imp_not = term![IMPLIES; x, y];
        let not_imp_not = term![NOT; imp_not];
        if let Some(cex) = find_model(&not_imp_not) {
            println!("Inputs:");
            for x_i in xs {
                println!("  {}", x_i);
            }
            println!("Inlined:");
            for x_i in ys {
                println!("  {}", x_i);
            }
            println!("Counterexample to inputs->outputs:");
            for (n, v) in &cex {
                println!("  {} -> {}", n, v);
            }
            panic!("Invalid inline");
        }
        assert!(!check_sat(&not_imp));
        assert!(!check_sat(&not_imp_not));
    }

    #[test]
    fn test_single_contra() {
        sub_test(vec![term![EQ; b_var("x"), term![NOT; b_var("x")]]], 1);
    }

    #[test]
    fn test_sat_cycle() {
        sub_test(
            vec![
                term![EQ; b_var("x"), term![NOT; b_var("y")]],
                term![EQ; b_var("y"), term![NOT; b_var("x")]],
            ],
            1,
        );
    }

    #[test]
    fn test_unsat_cycle() {
        sub_test(
            vec![
                term![EQ; b_var("x"), term![NOT; b_var("y")]],
                term![EQ; b_var("y"), b_var("x")],
            ],
            1,
        );
    }

    #[test]
    fn test_rolling_defs() {
        sub_test(
            vec![
                term![EQ; b_var("x"), term![NOT; b_var("y")]],
                term![EQ; b_var("z"), b_var("x")],
                term![EQ; b_var("a"), term![XOR; b_var("q"), b_var("y")]],
                term![XOR; b_var("a"), b_var("y")],
            ],
            1,
        );
    }
}
