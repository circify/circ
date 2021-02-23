use crate::ir::term::*;
use crate::ir::term::extras::*;
use std::collections::HashSet;
use log::debug;

pub struct Inliner<'a> {
    /// Map from variables to their values.
    /// Invariant: no key variable in in any value variable.
    /// Invariant: one a key appears in this map, it is never removed.
    substs: TermMap<Term>,
    /// The substitution cache.
    /// Must be reinitialized when `substs` are updated.
    /// Invariant: no key variable from `substs` is in any value of the cache.
    subst_cache: TermMap<Term>,

    /// A map from variable terms, to `substs` keys whose values contain them.
    variable_uses: TermMap<TermSet>,

    /// Variables that are "protected": they should not be eliminated.
    protected: &'a HashSet<String>,
}

impl<'a> Inliner<'a> {
    fn new(protected: &'a HashSet<String>) -> Self {
        Self {
            substs: TermMap::new(),
            subst_cache: TermMap::new(),
            variable_uses: TermMap::new(),
            protected,
        }
    }

    /// Checks invariant that no key variable is in any `substs` value.
    /// Also checks that no key variable is in any `subst_cache` value.
    fn check_substs(&self) {
        let keys: HashSet<&Term> = self.substs.keys().collect();
        for (key, value) in &self.substs {
            for child in PostOrderIter::new(value.clone()) {
                assert!(!keys.contains(&child),
                    "Substituted variable {} is in the substitution for {}, {}", child, key, value);
            }
        }
        for (key, value) in &self.subst_cache {
            for child in PostOrderIter::new(value.clone()) {
                assert!(!keys.contains(&child),
                    "Substituted variable {} is in the cache for {}, {}", child, key, value);
            }
        }
    }

    /// Applies the current substitutions to `t`.
    fn apply(&mut self, t: &Term) -> Term {
        substitute_cache(t, &mut self.subst_cache)
    }


    /// Syntactically analyzes `t`, seeing if it has form
    ///
    ///    * `(= v t')` OR
    ///    * `(= t' v)`
    ///
    /// where `v` is not in `t'`.
    ///
    /// If such a condition is met, returns `(v, t')`.
    /// Prefers the first form, if both match.
    ///
    /// Will not return `v` which are protected.
    fn as_subst(&self, t: &Term) -> Option<(Term, Term)> {
        if let Op::Eq = &t.op {
            if let Op::Var(name, _) = &t.cs[0].op {
                if !self.protected.contains(name) && does_not_contain(t.cs[1].clone(), &t.cs[0]) {
                    return Some((t.cs[0].clone(), t.cs[1].clone()));
                }
            }
            if let Op::Var(name, _) = &t.cs[1].op {
                if !self.protected.contains(name) && does_not_contain(t.cs[0].clone(), &t.cs[1]) {
                    return Some((t.cs[1].clone(), t.cs[0].clone()));
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
        let subst_t = self.apply(t);
        if let Some((var, val)) = self.as_subst(&subst_t) {
            debug!(target: "circ::ir::opt::inline", "Inline: {} -> {}", var, Letified(val.clone()));
            // First, we must remove all `var` from `substs`.
            // We do this with substitution, with a cache.
            let mut var_cache = TermMap::new();
            let val_vars: Vec<Term> = PostOrderIter::new(val.clone()).into_iter().filter(|t| t.is_var()).collect();
            var_cache.insert(var.clone(), val.clone());
            // For each substs key which maps to value with `var` in it,
            for prior_key in self.variable_uses.remove(&var).into_iter().flatten() {
                // substitute `var` out of that substs value,
                let prior_val = self.substs.get_mut(&prior_key).expect("Corrupted variable use");
                *prior_val = substitute_cache(prior_val, &mut var_cache);
                // and mark that the prior key uses each variable in `val`
                for newly_used in &val_vars {
                    let uses = self.variable_uses.entry(newly_used.clone()).or_insert(TermSet::new());
                    uses.insert(prior_key.clone());
                }
                // note that we removed all uses of `var` in the for loop iterator above.
            }
            self.substs.insert(var, val);
            // Since we've modified the substitutions, refesh the cache.
            self.subst_cache = self.substs.clone();

            // Comment out?
            //self.check_substs();

            None
        } else {
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
pub fn inline(assertions: &mut Vec<Term>, public_inputs: &HashSet<String>) {
    let mut new_assertions = Vec::new();
    let mut inliner = Inliner::new(public_inputs);
    for assertion in assertions.drain(..) {
        if let Some(rewritten_assertion) = inliner.ingest_term(&assertion) {
            new_assertions.push(rewritten_assertion);
        }
    }
    *assertions = new_assertions;
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::target::smt::{find_model, check_sat};

    fn b_var(b: &str) -> Term {
        leaf_term(Op::Var(format!("{}", b), Sort::Bool))
    }

    fn b_lit(b: bool) -> Term {
        leaf_term(Op::Const(Value::Bool(b)))
    }

    const B_AND: Op = Op::BoolNaryOp(BoolNaryOp::And);
    const B_OR: Op = Op::BoolNaryOp(BoolNaryOp::Or);
    const B_XOR: Op = Op::BoolNaryOp(BoolNaryOp::Xor);

    fn sub_test(xs: Vec<Term>) {
        let mut ys = xs.clone();
        let p = HashSet::new();
        inline(&mut ys, &p);
        let x = term(Op::BoolNaryOp(BoolNaryOp::And), xs.clone());
        let y = term(Op::BoolNaryOp(BoolNaryOp::And), ys.clone());
        let imp = term![Op::Implies; x.clone(), y.clone()];
        let not_imp = term![Op::Not; imp];
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
        let imp_not = term![Op::Implies; x, y];
        let not_imp_not = term![Op::Not; imp_not];
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
        assert_eq!(check_sat(&not_imp), false);
        assert_eq!(check_sat(&not_imp_not), false);
    }

    #[test]
    fn test_single_contra() {
        sub_test(vec![
            term![Op::Eq; b_var("x"), term![Op::Not; b_var("x")]],
        ]);
    }

    #[test]
    fn test_sat_cycle() {
        sub_test(vec![
            term![Op::Eq; b_var("x"), term![Op::Not; b_var("y")]],
            term![Op::Eq; b_var("y"), term![Op::Not; b_var("x")]],
        ]);
    }

    #[test]
    fn test_unsat_cycle() {
        sub_test(vec![
            term![Op::Eq; b_var("x"), term![Op::Not; b_var("y")]],
            term![Op::Eq; b_var("y"), b_var("x")],
        ]);
    }

    #[test]
    fn test_rolling_defs() {
        sub_test(vec![
            term![Op::Eq; b_var("x"), term![Op::Not; b_var("y")]],
            term![Op::Eq; b_var("z"), b_var("x")],
            term![Op::Eq; b_var("a"), term![B_XOR; b_var("q"), b_var("y")]],
            term![B_XOR; b_var("a"), b_var("y")],
        ]);
    }
}
