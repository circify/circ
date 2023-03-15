use crate::ir::term::*;

use log::trace;

/// A rewriting pass.
pub trait RewritePass {
    /// Visit (and possibly rewrite) a term.
    /// Given the original term and a function to get its rewritten childen.
    /// Returns a term if a rewrite happens.
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term>;

    /// What
    fn visit_cache(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        cache: &TermMap<Term>,
    ) -> Option<Term> {
        let get_children = || -> Vec<Term> {
            orig.cs()
                .iter()
                .map(|c| cache.get(c).unwrap())
                .cloned()
                .collect()
        };
        self.visit(computation, orig, get_children)
    }

    fn traverse(&mut self, computation: &mut Computation) {
        self.traverse_full(computation, false, true);
    }

    fn traverse_full(
        &mut self,
        computation: &mut Computation,
        precompute: bool,
        persistent_arrays: bool,
    ) {
        let mut cache = TermMap::<Term>::default();
        let mut children_added = TermSet::default();
        let mut stack = Vec::new();
        if persistent_arrays {
            stack.extend(
                computation
                    .persistent_arrays
                    .iter()
                    .map(|(_name, final_term)| final_term.clone()),
            );
        }
        stack.extend(computation.outputs.iter().cloned());
        if precompute {
            stack.extend(computation.precomputes.outputs().values().cloned());
        }
        while let Some(top) = stack.pop() {
            if !cache.contains_key(&top) {
                // was it missing?
                if children_added.insert(top.clone()) {
                    stack.push(top.clone());
                    stack.extend(top.cs().iter().filter(|c| !cache.contains_key(c)).cloned());
                } else {
                    let new_t_opt = self.visit_cache(computation, &top, &cache);
                    let new_t = new_t_opt.unwrap_or_else(|| {
                        term(
                            top.op().clone(),
                            top.cs()
                                .iter()
                                .map(|c| cache.get(c).unwrap())
                                .cloned()
                                .collect(),
                        )
                    });
                    cache.insert(top.clone(), new_t);
                }
            }
        }
        if persistent_arrays {
            for (_name, final_term) in &mut computation.persistent_arrays {
                let new_final_term = cache.get(final_term).unwrap().clone();
                trace!("Array {} -> {}", final_term, new_final_term);
                *final_term = new_final_term;
            }
        }
        computation.outputs = computation
            .outputs
            .iter()
            .map(|o| cache.get(o).unwrap().clone())
            .collect();
        if precompute {
            let os = computation.precomputes.outputs().clone();
            for (name, old_term) in os {
                let new_term = cache.get(&old_term).unwrap().clone();
                computation.precomputes.change_output(&name, new_term);
            }
        }
    }
}

/// An analysis pass that repeated sweeps all terms, visiting them, untill a pass makes no more
/// progress.
pub trait ProgressAnalysisPass {
    /// The visit function. Returns whether progress was made.
    fn visit(&mut self, term: &Term) -> bool;
    /// Repeatedly sweep till progress is no longer made.
    fn traverse(&mut self, computation: &Computation) {
        let mut progress = true;
        let mut order = Vec::new();
        let mut visited = TermSet::default();
        let mut stack: Vec<Term> = computation.outputs.clone();

        while let Some(top) = stack.pop() {
            stack.extend(top.cs().iter().filter(|c| !visited.contains(c)).cloned());
            // was it missing?
            if visited.insert(top.clone()) {
                order.push(top);
            }
        }
        while progress {
            progress = false;
            for t in &order {
                progress = self.visit(t) || progress;
            }
            for t in order.iter().rev() {
                progress = self.visit(t) || progress;
            }
        }
    }
}
