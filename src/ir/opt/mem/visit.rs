use crate::ir::term::*;

/// A rewriting pass.
pub trait RewritePass {
    /// Visit (and possibly rewrite) a term.
    /// Given the original term and a function to get its rewritten childen.
    /// Returns a term if a rewrite happens.
    fn visit<F: Fn() -> Vec<Term>>(&mut self, orig: &Term, rewritten_children: F) -> Option<Term>;
    fn traverse(&mut self, computation: &mut Computation) {
        let mut cache = TermMap::<Term>::new();
        let mut children_added = TermSet::new();
        let mut stack = Vec::new();
        stack.extend(computation.outputs.iter().cloned());
        while let Some(top) = stack.pop() {
            if !cache.contains_key(&top) {
                // was it missing?
                if children_added.insert(top.clone()) {
                    let get_children = || -> Vec<Term> {
                        top.cs
                            .iter()
                            .map(|c| cache.get(c).unwrap())
                            .cloned()
                            .collect()
                    };
                    let new_t_opt = self.visit(&top, get_children);
                    let new_t = new_t_opt.unwrap_or_else(|| term(top.op.clone(), get_children()));
                    cache.insert(top.clone(), new_t);
                } else {
                    stack.push(top.clone());
                    stack.extend(top.cs.iter().filter(|c| !cache.contains_key(c)).cloned());
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
            // was it missing?
            if visited.insert(top.clone()) {
                order.push(top);
            } else {
                stack.extend(top.cs.iter().filter(|c| !visited.contains(c)).cloned());
            }
        }
        while progress {
            progress = false;
            for t in &order {
                progress = progress || self.visit(t);
            }
            for t in order.iter().rev() {
                progress = progress || self.visit(t);
            }
        }
    }
}

/// A visitor for traversing terms, and visiting the array-related parts.
///
/// Visits:
/// * EQs over arrays
/// * Constant arrays
/// * ITEs over arrays
/// * array variables
/// * STOREs
/// * SELECTs
///
/// Crashes on:
/// * arrays in tuples
///
/// For the EQs and SELECTs, you have the ability to (optionally) return a replacement for the
/// term. This can be used to "cut" the array out of the term, since EQs and SELECTs are how
/// information leaves an array.
///
/// All visitors receive the original term and the rewritten children.
pub trait MemVisitor {
    /// Visit a const array
    fn visit_const_array(&mut self, _orig: &Term, _key_sort: &Sort, _val: &Term, _size: usize) {}
    /// Visit an equality, whose children are `a` and `b`.
    fn visit_eq(&mut self, _orig: &Term, _a: &Term, _b: &Term) -> Option<Term> {
        None
    }
    /// Visit an array-valued ITE
    fn visit_ite(&mut self, _orig: &Term, _c: &Term, _t: &Term, _f: &Term) {}
    /// Visit a STORE
    fn visit_store(&mut self, _orig: &Term, _a: &Term, _k: &Term, _v: &Term) {}
    /// Visit a SELECT
    fn visit_select(&mut self, _orig: &Term, _a: &Term, _k: &Term) -> Option<Term> {
        None
    }
    fn visit_var(&mut self, _orig: &Term, _name: &String, _s: &Sort) {}

    /// Traverse a node, visiting memory-related terms.
    ///
    /// Can be used to remove memory-related terms by replacing the EQs and SELECTs which extract
    /// other terms from them.
    ///
    /// Returns the transformed term.
    fn traverse(&mut self, node: &Term) -> Term {
        let mut cache = TermMap::<Term>::new();
        for t in PostOrderIter::new(node.clone()) {
            let c_get = |x: &Term| cache.get(x).unwrap();
            let get = |i: usize| c_get(&t.cs[i]);
            let new_t_opt = {
                let s = check(&t);
                match &s {
                    Sort::Array(_, _, _) => {
                        match &t.op {
                            Op::Var(name, s) => {
                                self.visit_var(&t, name, s);
                            }
                            Op::Ite => {
                                self.visit_ite(&t, get(0), get(1), get(2));
                            }
                            Op::Store => {
                                self.visit_store(&t, get(0), get(1), get(2));
                            }
                            Op::ConstArray(s, n) => {
                                self.visit_const_array(&t, s, get(0), *n);
                            }
                            Op::Field(_) => panic!("array in tuple during mem pass: {}", t),
                            _ => {}
                        };
                        None
                    }
                    _ => match &t.op {
                        Op::Eq => {
                            let a = get(0);
                            if let Sort::Array(_, _, _) = check(&a) {
                                self.visit_eq(&t, a, get(1))
                            } else {
                                None
                            }
                        }
                        Op::Select => self.visit_select(&t, get(0), get(1)),
                        _ => None,
                    },
                }
            };
            // replace children of in cache
            let mut new_cs: Vec<Term> = Vec::new();
            for x in t.cs.iter() {
                new_cs.push(cache.get(&x).unwrap_or_else(|| x).clone());
            }
            let new_t = term(t.op.clone(), new_cs);

            cache.insert(t.clone(), new_t_opt.unwrap_or_else(|| new_t.clone()));
        }
        cache.remove(node).unwrap()
    }
}

pub trait ProgressVisitor: MemVisitor {
    fn reset_progress(&mut self);
    fn check_progress(&self) -> bool;

    fn traverse_to_fixpoint(&mut self, a: &Term) {
        self.traverse(a);
        while self.check_progress() {
            self.reset_progress();
            self.traverse(a);
        }
    }
}
