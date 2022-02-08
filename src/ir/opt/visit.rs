use crate::ir::term::*;

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
    fn traverse(&mut self, computation: &mut Computation) {
        let mut cache = TermMap::<Term>::new();
        let mut children_added = TermSet::new();
        let mut stack = Vec::new();
        stack.extend(computation.outputs.iter().cloned());
        while let Some(top) = stack.pop() {
            if !cache.contains_key(&top) {
                // was it missing?
                if children_added.insert(top.clone()) {
                    stack.push(top.clone());
                    stack.extend(top.cs.iter().filter(|c| !cache.contains_key(c)).cloned());
                } else {
                    let get_children = || -> Vec<Term> {
                        top.cs
                            .iter()
                            .map(|c| cache.get(c).unwrap())
                            .cloned()
                            .collect()
                    };
                    let new_t_opt = self.visit(computation, &top, get_children);
                    let new_t = new_t_opt.unwrap_or_else(|| term(top.op.clone(), get_children()));
                    cache.insert(top.clone(), new_t);
                }
            }
        }
        computation.outputs = computation
            .outputs
            .iter()
            .map(|o| cache.get(o).unwrap().clone())
            .collect();
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
        let mut visited = TermSet::new();
        let mut stack = Vec::new();
        stack.extend(computation.outputs.iter().cloned());
        while let Some(top) = stack.pop() {
            stack.extend(top.cs.iter().filter(|c| !visited.contains(c)).cloned());
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
