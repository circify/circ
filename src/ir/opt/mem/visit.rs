use crate::ir::term::*;

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
                let s = check(t.clone()).unwrap();
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
                            _ => {}
                        };
                        None
                    }
                    _ => match &t.op {
                        Op::Eq => {
                            let a = get(0);
                            if let Sort::Array(_, _, _) = check(a.clone()).unwrap() {
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
            cache.insert(t.clone(), new_t_opt.unwrap_or_else(|| t.clone()));
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
