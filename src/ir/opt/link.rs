//! Link Computation call terms

use fxhash::FxHashMap as HashMap;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

/// A recursive linker.
struct Linker<'f> {
    /// Original source for Functions
    cs: &'f Computations,
    /// Map from names to call-free computations
    cache: HashMap<String, Computation>,
}

/// Compute the term that corresponds to a function call.
///
/// ## Arguments
///
/// * `callee`: the called function
/// * `arg_values`: the argument values, sorted by variable names
///
/// ## Returns
///
/// A (tuple) term that corresponds to the output on those inputs
///
/// ## Note
///
/// This function **does not** recursively link.
pub fn link_one(callee: &Computation, values: Vec<Term>) -> Term {
    let mut substitution_map: TermMap<Term> = TermMap::default();
    let names = callee.metadata.ordered_input_names();
    assert_eq!(names.len(), values.len());
    for (name, value) in names.into_iter().zip(values) {
        let sort = callee.metadata.input_sort(&name).clone();
        substitution_map.insert(leaf_term(Op::Var(name, sort)), value);
    }
    term(
        Op::Tuple,
        callee
            .outputs()
            .iter()
            .map(|o| extras::substitute_cache(o, &mut substitution_map))
            .collect(),
    )
}

impl<'f> Linker<'f> {
    /// Ensure that a totally linked version of `name` is in the cache.
    fn link_all(&mut self, name: &str) {
        if !self.cache.contains_key(name) {
            let mut c = self.cs.get(name).clone();
            for t in c.terms_postorder() {
                if let Op::Call(callee_name, ..) = &t.op() {
                    self.link_all(callee_name);
                }
            }

            self.traverse(&mut c);
            let present = self.cache.insert(name.into(), c);
            assert!(present.is_none());
        }
    }
}

/// Rewrites a term, inlining function calls along the way.
///
/// Assumes that the callees are already inlined. Panics otherwise.
impl<'f> RewritePass for Linker<'f> {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        if let Op::Call(fn_name, _, _) = &orig.op() {
            let callee = self.cache.get(fn_name).expect("missing inlined callee");
            let term = link_one(callee, rewritten_children());
            Some(term)
        } else {
            None
        }
    }
}

/// Link all calls within a function set.
pub fn link_all_function_calls(cs: &mut Computations) {
    let mut linker = Linker {
        cs,
        cache: Default::default(),
    };
    for name in cs.comps.keys() {
        linker.link_all(name);
    }

    *cs = Computations {
        comps: linker.cache.into_iter().collect(),
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bool_arg_nonrec() {
        let mut cs = text::parse_computations(
            b"
            (computations
                (myxor
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        (xor a b false false)
                    )
                )
                (main
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        (and false ((field 0) ((call myxor (bool bool) (tuple bool)) a b)))
                    )
                )
            )",
        );
        let expected = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                    (precompute () () (#t ))
                    (and false ((field 0) (tuple (xor a b false false))))
                )
            ",
        );
        link_all_function_calls(&mut cs);
        let c = cs.get("main").clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn scalar_arg_nonrec() {
        let mut cs = text::parse_computations(
            b"
                (computations
                    (myxor
                        (computation
                            (metadata (parties ) (inputs (a bool) (b (bv 4))) (commitments))
                            (precompute () () (#t ))
                            (bvxor (ite a #x0 #x1) b)
                        )
                    )
                    (main
                        (computation
                            (metadata (parties ) (inputs (c bool)) (commitments))
                            (precompute () () (#t ))
                            (bvand #xf ((field 0) ((call myxor (bool (bv 4)) (tuple (bv 4))) c #x4 )))
                        )
                    )
                )",
        );

        let expected = text::parse_computation(
            b"
                    (computation
                        (metadata (parties ) (inputs (c bool)) (commitments))
                        (precompute () () (#t ))
                        (bvand #xf ((field 0) (tuple (bvxor (ite c #x0 #x1) #x4))))
                    )
                ",
        );
        link_all_function_calls(&mut cs);
        let c = cs.get("main").clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn nested_calls() {
        let mut cs = text::parse_computations(
            b"
                (computations
                    (foo
                        (computation
                            (metadata (parties ) (inputs (a bool)) (commitments))
                            (precompute () () (#t ))
                            (not a)
                        )
                    )
                    (bar
                        (computation
                            (metadata (parties ) (inputs (a bool)) (commitments))
                            (precompute () () (#t ))
                            (xor ((field 0) ((call foo (bool) (tuple bool)) a)) true)
                        )
                    )
                    (main
                        (computation
                            (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                            (precompute () () (#t ))
                            ((field 0) ((call bar (bool) (tuple bool)) a))
                        )
                    )
                )",
        );

        let expected = text::parse_computation(
            b"
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        ((field 0) (tuple (xor ((field 0) (tuple (not a))) true)))
                    )
                ",
        );
        link_all_function_calls(&mut cs);
        let c = cs.get("main").clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn multiple_calls() {
        let mut cs = text::parse_computations(
            b"
                (computations

                    (foo
                        (computation
                            (metadata (parties ) (inputs (a bool)) (commitments))
                            (precompute () () (#t ))
                            (not a)
                        )
                    )
                    (bar
                        (computation
                            (metadata (parties ) (inputs (a bool)) (commitments))
                            (precompute () () (#t ))
                            (xor ((field 0) ((call foo (bool) (tuple bool)) a)) true)
                        )
                    )
                    (main
                        (computation
                            (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                            (precompute () () (#t ))
                            (and
                                ((field 0) ((call foo (bool) (tuple bool)) a))
                                ((field 0) ((call foo (bool) (tuple bool)) b))
                                ((field 0) ((call bar (bool) (tuple bool)) a))
                            )
                        )
                    )
                )",
        );

        let expected = text::parse_computation(
            b"
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        (and
                            ((field 0) (tuple (not a)))
                            ((field 0) (tuple (not b)))
                            ((field 0) (tuple (xor ((field 0) (tuple (not a))) true)))
                        )
                    )
                ",
        );
        link_all_function_calls(&mut cs);
        let c = cs.get("main").clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn term_hconsed() {
        let mut cs = text::parse_computations(
            b"
                (computations
                    (myxor
                        (computation
                            (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                            (precompute () () (#t ))
                            (xor a b false false)
                        )
                    )
                    (main
                        (computation
                            (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                            (precompute () () (#t ))
                            (and false ((field 0) ( (call myxor (bool bool) (tuple bool)) a b )))
                        )
                    )
                )",
        );
        let expected = text::parse_computation(
            b"
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        (and false ((field 0) (tuple (xor a b false false))))
                    )
                ",
        );

        let comp = cs.get("main");
        let mut cache: std::collections::HashMap<Term, usize> = std::collections::HashMap::new();
        for t in comp.outputs.iter() {
            cache.insert(t.clone(), 1);
        }
        link_all_function_calls(&mut cs);
        let c = cs.get("main").clone();
        assert_eq!(c, expected);
    }
}
