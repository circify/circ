//! Parsing and expanding conditional stores.

use crate::ir::term::*;

use super::visit::RewritePass;

/// Parse `ite` or `store` as a conditional store (arr, idx, val, guard)
fn parse_cond_store(term: &Term) -> Option<ConditionalStore> {
    if let (&Op::Ite, [guard, true_, false_]) = term.parts() {
        match true_.parts() {
            (&Op::Store, [arr, idx, val]) if arr == false_ => {
                // (ite COND (store ARR IDX VAL) ARR)
                return Some(ConditionalStore {
                    arr: arr.clone(),
                    idx: idx.clone(),
                    val: val.clone(),
                    guard: guard.clone(),
                });
            }
            _ => {}
        }
        match false_.parts() {
            (&Op::Store, [arr, idx, val]) if arr == false_ => {
                // (ite COND ARR (store ARR IDX VAL))
                return Some(ConditionalStore {
                    arr: arr.clone(),
                    idx: idx.clone(),
                    val: val.clone(),
                    guard: term![NOT; guard.clone()],
                });
            }
            _ => {}
        }
    }
    if let (&Op::Store, [arr, idx, val]) = term.parts() {
        if let (&Op::Ite, [guard, true_, false_]) = val.parts() {
            match false_.parts() {
                (&Op::Select, [arr2, idx2]) if arr == arr2 && idx == idx2 => {
                    // (store ARR IDX (ite COND VAL (select ARR IDX)))
                    return Some(ConditionalStore {
                        arr: arr.clone(),
                        idx: idx.clone(),
                        val: true_.clone(),
                        guard: guard.clone(),
                    });
                }
                _ => {}
            }
            match true_.parts() {
                (&Op::Select, [arr2, idx2]) if arr == arr2 && idx == idx2 => {
                    // (store ARR IDX (ite COND (select ARR IDX) VAL))
                    return Some(ConditionalStore {
                        arr: arr.clone(),
                        idx: idx.clone(),
                        val: false_.clone(),
                        guard: term![NOT; guard.clone()],
                    });
                }
                _ => {}
            }
        }
    }
    None
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
