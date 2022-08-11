//! Link function call terms

use fxhash::FxHashMap as HashMap;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

/// A recursive linker.
struct Linker<'f> {
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
/// This function **does not** recursively link.
pub fn link_one(arg_names: &Vec<String>, arg_values: Vec<Term>, callee: &Computation) -> Term {
    // println!("arg_names: {:?}", arg_names);
    // println!("arg_terms: {:?}", arg_values);
    let mut sub_map: TermMap<Term> = TermMap::new();
    assert_eq!(arg_names.len(), arg_values.len());
    for (n, v) in arg_names.into_iter().zip(arg_values) {
        let ssa_names = callee.metadata.input_ssa_name_from_nice_name(n);
        // println!("{:?}", ssa_names);
        if ssa_names.len() == 1 {
            let s = callee.metadata.input_sort(&ssa_names[0].0).clone();
            sub_map.insert(leaf_term(Op::Var(ssa_names[0].0.clone(), s)), v);
        } else {
            for (s_name, index) in ssa_names {
                let s = callee.metadata.input_sort(&s_name).clone();
                sub_map.insert(
                    leaf_term(Op::Var(s_name, s)),
                    term![Op::Select; v.clone(), bv_lit(index, 32)],
                );
            }
        }
    }
    term(
        Op::Tuple,
        callee
            .outputs()
            .iter()
            .map(|o| extras::substitute_cache(o, &mut sub_map))
            .collect(),
    )
}

impl<'f> Linker<'f> {
    /// Ensure that a totally linked version of `name` is in the cache.
    fn link_all(&mut self, name: &str) {
        if !self.cache.contains_key(name) {
            let mut c = self.fs.get_comp(name).unwrap().clone();
            for t in c.terms_postorder() {
                if let Op::Call(callee_name, ..) = &t.op {
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
        if let Op::Call(fn_name, arg_names, _, _) = &orig.op {
            let callee = self.cache.get(fn_name).expect("missing inlined callee");
            let term = link_one(arg_names, rewritten_children(), callee);
            Some(term)
        } else {
            None
        }
    }
}

/// Link all calls within a function set.
pub fn link_all_function_calls(fs: &mut Functions) {
    let mut linker = Linker {
        fs,
        cache: Default::default(),
    };
    for name in fs.computations.keys() {
        linker.link_all(name);
    }

    *fs = Functions {
        computations: linker.cache.into_iter().collect(),
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

    #[test]
    fn term_hconsed() {
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

        let comp = fs.get_comp("main").unwrap();
        let mut cache: std::collections::HashMap<Term, usize> = std::collections::HashMap::new();
        for t in comp.outputs.iter() {
            cache.insert(t.clone(), 1);
        }
        for t in comp.outputs.iter() {
            let get_children = || -> Vec<Term> { t.cs.iter().cloned().collect() };
            if cache.contains_key(&term(t.op.clone(), get_children())) {
                println!("Got you1!!!!!");
            }
        }
        link_all_function_calls(&mut fs);
        let c = fs.get_comp("main").unwrap().clone();
        for t in c.outputs.iter() {
            if cache.contains_key(t) {
                println!("Got you2!!!!!");
            }
        }
        assert_eq!(c, expected);
    }
}
