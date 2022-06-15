//! Inline function call terms

use fxhash::FxHashMap as HashMap;

use crate::ir::term::*;
use crate::ir::opt::visit::RewritePass;

/// A recursive inliner.
struct Inliner<'f> {
    /// Original source for functions
    fs: &'f Functions,
    /// Map from names to call-free computations
    cache: HashMap<String, Computation>,
}

/// Compute the term that corresponds to a function call.
///
/// ## Arguments
///
/// * `arg_names`: the argument names, in order
/// * `arg_values`: the argument values, in the same order
/// * `callee`: the called function
///
/// ## Returns
///
/// A (tuple) term that corresponds to the output on those inputs
///
/// ## Note
///
/// This function **does not** recursively inline.
fn inline_one(arg_names: &Vec<String>, arg_values: Vec<Term>, callee: &Computation) -> Term {
    let mut sub_map: TermMap<Term> = arg_names
        .into_iter()
        .zip(arg_values)
        .map(|(n, v)| {
            let s = callee.metadata.input_sort(n).clone();
            (leaf_term(Op::Var(n.clone(), s)), v)
        })
        .collect();
    term(
        Op::Tuple,
        callee
            .outputs()
            .iter()
            .map(|o| extras::substitute_cache(o, &mut sub_map))
            .collect(),
    )
}

impl<'f> Inliner<'f> {
    /// Ensure that a totally inlined version of `name` is in the cache.
    fn inline_all(&mut self, name: &str) {
        if !self.cache.contains_key(name) {
            let mut c = self.fs.get_comp(name).unwrap().clone();
            for t in c.terms_postorder() {
                if let Op::Call(callee_name, ..) = &t.op {
                    self.inline_all(callee_name);
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
impl<'f> RewritePass for Inliner<'f> {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        if let Op::Call(fn_name, arg_names, _, _) = &orig.op {
            let callee = self.cache.get(fn_name).expect("missing inlined callee");
            let term = inline_one(arg_names, rewritten_children(), callee);
            Some(term)
        } else {
            None
        }
    }
}

/// Inline all calls within a function set.
pub fn link_all_function_calls(fs: &mut Functions) {
    let mut inliner = Inliner {
        fs,
        cache: Default::default(),
    };
    for name in fs.computations.keys() {
        inliner.inline_all(name);
    }
    *fs = Functions {
        computations: inliner.cache.into_iter().collect(),
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bool_arg_nonrec() {
        let mut fs = text::parse_functions(
            b"
            (functions
                (
            (myxor
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    (xor a b false false)
                )
            )
            (main
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    (and false ((field 0) ( (call myxor (a b) (bool bool) (bool)) a b )))
                )
            )
            )
            )",
        );
        let expected = text::parse_computation(
            b"
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    (and false ((field 0) (tuple (xor a b false false))))
                )
            ",
        );
        link_all_function_calls(&mut fs);
        let c = fs.get_comp("main").unwrap().clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn scalar_arg_nonrec() {
        let mut fs = text::parse_functions(
            b"
            (functions
                (
            (myxor
                (computation
                    (metadata () ((a bool) (b (bv 4))) ())
                    (bvxor (ite a #x0 #x1) b)
                )
            )
            (main
                (computation
                    (metadata () ((c bool)) ())
                    (bvand #xf ((field 0) ( (call myxor (a b) (bool (bv 4)) ((bv 4))) c #x4 )))
                )
            )
            )
            )",
        );

        let expected = text::parse_computation(
            b"
                (computation
                    (metadata () ((c bool)) ())
                    (bvand #xf ((field 0) (tuple (bvxor (ite c #x0 #x1) #x4))))
                )
            ",
        );
        link_all_function_calls(&mut fs);
        let c = fs.get_comp("main").unwrap().clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn nested_calls() {
        let mut fs = text::parse_functions(
            b"
            (functions
                (
            (foo
                (computation
                    (metadata () ((a bool)) ())
                    (not a)
                )
            )
            (bar
                (computation
                    (metadata () ((a bool)) ())
                    (xor ((field 0) ((call foo (a) (bool) (bool)) a)) true)
                )
            )
            (main
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    ((field 0) ((call bar (a) (bool) (bool)) a))
                )
            )
            )
            )",
        );

        let expected = text::parse_computation(
            b"
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    ((field 0) (tuple (xor ((field 0) (tuple (not a))) true)))
                )
            ",
        );
        link_all_function_calls(&mut fs);
        let c = fs.get_comp("main").unwrap().clone();
        assert_eq!(c, expected);
    }

    #[test]
    fn multiple_calls() {
        let mut fs = text::parse_functions(
            b"
            (functions
                (
            (foo
                (computation
                    (metadata () ((a bool)) ())
                    (not a)
                )
            )
            (bar
                (computation
                    (metadata () ((a bool)) ())
                    (xor ((field 0) ((call foo (a) (bool) (bool)) a)) true)
                )
            )
            (main
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    (and
                      ((field 0) ((call foo (a) (bool) (bool)) a))
                      ((field 0) ((call foo (a) (bool) (bool)) b))
                      ((field 0) ((call bar (a) (bool) (bool)) a))
                    )
                )
            )
            )
            )",
        );

        let expected = text::parse_computation(
            b"
                (computation
                    (metadata () ((a bool) (b bool)) ())
                    (and
                    ((field 0) (tuple (not a)))
                    ((field 0) (tuple (not b)))
                    ((field 0) (tuple (xor ((field 0) (tuple (not a))) true)))
                    )
                )
            ",
        );
        link_all_function_calls(&mut fs);
        let c = fs.get_comp("main").unwrap().clone();
        assert_eq!(c, expected);
    }
}
