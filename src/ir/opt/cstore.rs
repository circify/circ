//! Parsing and expanding conditional stores.

use crate::ir::term::*;

use super::visit::RewritePass;

/// Parse `ite` as a conditional store (arr, idx, val, guard)
fn parse_cond_store(ite: &Term) -> Option<ConditionalStore> {
    if ite.op() == &Op::Ite && ite.cs()[1].op() == &Op::Store && ite.cs()[1].cs()[0] == ite.cs()[2]
    {
        // (ite COND (store ARR IDX VAL) ARR)
        Some(ConditionalStore {
            arr: ite.cs()[2].clone(),
            idx: ite.cs()[1].cs()[1].clone(),
            val: ite.cs()[1].cs()[2].clone(),
            guard: ite.cs()[0].clone(),
        })
    } else if ite.op() == &Op::Ite
        && ite.cs()[2].op() == &Op::Store
        && ite.cs()[2].cs()[0] == ite.cs()[1]
    {
        // (ite COND ARR (store ARR IDX VAL))
        Some(ConditionalStore {
            arr: ite.cs()[1].clone(),
            idx: ite.cs()[2].cs()[1].clone(),
            val: ite.cs()[2].cs()[2].clone(),
            guard: term![NOT; ite.cs()[0].clone()],
        })
        // could do things like: (store ARR IDX (ite COND VAL (select ARR IDX)))
    } else {
        None
    }
}

#[derive(Debug)]
/// Data about a conditional store: term = (ite guard (store arr idx val) arr)
///
/// The store field is (store arr idx val)
struct ConditionalStore {
    arr: Term,
    idx: Term,
    val: Term,
    guard: Term,
}

struct Parser;

impl RewritePass for Parser {
    fn visit<F: Fn() -> Vec<Term>>(&mut self, _: &mut Computation, _: &Term, _: F) -> Option<Term> {
        unreachable!("implemeneted visit_cache")
    }

    fn visit_cache(
        &mut self,
        _: &mut Computation,
        orig: &Term,
        cache: &TermMap<Term>,
    ) -> Option<Term> {
        if let Some(c_store) = parse_cond_store(orig) {
            let a = cache.get(&c_store.arr).unwrap().clone();
            let i = cache.get(&c_store.idx).unwrap().clone();
            let v = cache.get(&c_store.val).unwrap().clone();
            let c = cache.get(&c_store.guard).unwrap().clone();
            Some(term![Op::CStore; a, i, v, c])
        } else {
            None
        }
    }
}

struct Expander;

impl RewritePass for Expander {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        if let Op::CStore = orig.op() {
            let mut cs = rewritten_children();
            let c = cs.pop().unwrap();
            let v = cs.pop().unwrap();
            let i = cs.pop().unwrap();
            let a = cs.pop().unwrap();
            assert!(cs.is_empty());
            Some(term![Op::Ite; c, term![Op::Store; a.clone(), i, v], a])
        } else {
            None
        }
    }
}

/// Identify combinations of STORE and ITE which are actually CSTORES.
pub fn parse(c: &mut Computation) {
    Parser.traverse(c);
}

/// Replace CSTORES with combinations of STORE and ITE.
pub fn expand(c: &mut Computation) {
    Expander.traverse(c);
}

#[cfg(test)]
mod test {
    use super::*;

    fn n_stores(c: &Computation) -> usize {
        c.terms_postorder().filter(|t| t.op() == &Op::Store).count()
    }

    #[test]
    fn no_cstores() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs (a bool) (b bool) (c (mod 5))) (commitments))
                (precompute () () (#t ))
                (set_default_modulus 5
                    (let
                        (
                            ('0 (#a (mod 5) #f1 4 ()))
                            ('1 (store '0 #f0 c))
                            ('2 (cstore '1  #f0 #f0 a))
                            ('3 (cstore '2  #f0 #f0 b))
                        )
                        '3
                    )
                )
            )
            ",
        );
        let c2 = c.clone();
        assert_eq!(n_stores(&c), 1);
        parse(&mut c);
        assert_eq!(n_stores(&c), 1);
        expand(&mut c);
        assert_eq!(n_stores(&c), 3);
        parse(&mut c);
        assert_eq!(c, c2);
    }

    #[test]
    fn cstores() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs (a bool) (b bool) (c (mod 5))) (commitments))
                (precompute () () (#t ))
                (set_default_modulus 5
                    (let
                        (
                            ('0 (#a (mod 5) #f1 4 ()))
                            ('1 (store '0 #f0 c))
                            ('2 (ite a '1 '0))
                            ('3 (cstore '2  #f0 #f0 b))
                        )
                        '3
                    )
                )
            )
            ",
        );
        assert_eq!(n_stores(&c), 1);
        parse(&mut c);
        let c2 = c.clone();
        assert_eq!(n_stores(&c), 0);
        expand(&mut c);
        assert_eq!(n_stores(&c), 2);
        parse(&mut c);
        assert_eq!(c, c2);
    }
}
