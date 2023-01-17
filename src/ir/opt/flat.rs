//! Flatten terms

use crate::ir::term::*;
use std::rc::Rc;

enum Entry {
    Term(Rc<Term>),
    NaryTerm(Op, L<Term>, Option<Term>),
}

type L<T> = Rc<PersistentConcatList<T>>;

enum PersistentConcatList<T> {
    Leaf(Rc<T>),
    Concat(Vec<L<T>>),
}

impl<T: Clone> PersistentConcatList<T> {
    fn as_vec(this: L<T>) -> Vec<T> {
        let mut v = Vec::new();
        let mut stack = vec![this];
        while let Some(t) = stack.pop() {
            match &*t {
                PersistentConcatList::Leaf(t) => v.push((**t).clone()),
                PersistentConcatList::Concat(ts) => {
                    ts.iter().for_each(|c| stack.push(c.clone()));
                }
            }
        }
        v
    }
}

impl Entry {
    fn as_term(&mut self) -> Term {
        match self {
            Entry::Term(t) => (**t).clone(),
            Entry::NaryTerm(o, ts, maybe_term) => {
                if maybe_term.is_none() {
                    let v = PersistentConcatList::as_vec(ts.clone());
                    *maybe_term = Some(term(o.clone(), v));
                }
                maybe_term.as_ref().unwrap().clone()
            }
        }
    }
}

/// Flattening cache.
#[derive(Default)]
pub struct Cache(TermMap<Entry>);

impl Cache {
    /// Empty flattening.
    pub fn new() -> Self {
        Cache(TermMap::default())
    }
}

/// Traverse `term`, flattening n-ary operators.
pub fn flatten_nary_ops(term_: Term) -> Term {
    let mut c = Cache::new();
    flatten_nary_ops_cached(term_, &mut c)
}
/// Traverse `term`, flattening n-ary operators.
pub fn flatten_nary_ops_cached(term_: Term, Cache(ref mut rewritten): &mut Cache) -> Term {
    let mut parent_counts = TermMap::<usize>::default();
    for t in PostOrderIter::new(term_.clone()) {
        for c in t.cs().iter().cloned() {
            *parent_counts.entry(c).or_insert(0) += 1;
        }
    }

    // what does a term rewrite to?
    let mut stack = vec![(term_.clone(), false)];

    // Maps terms to their rewritten versions.
    while let Some((t, children_pushed)) = stack.pop() {
        if rewritten.contains_key(&t) {
            continue;
        }
        if !children_pushed {
            stack.push((t.clone(), true));
            stack.extend(t.cs().iter().map(|c| (c.clone(), false)));
            continue;
        }
        let entry = match &t.op() {
            // Don't flatten field*, since it does not help us.
            Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(PfNaryOp::Add) => {
                let mut children = Vec::new();
                for c in t.cs() {
                    match rewritten.get_mut(c).unwrap() {
                        Entry::Term(t) => {
                            children.push(Rc::new(PersistentConcatList::Leaf(t.clone())))
                        }
                        Entry::NaryTerm(o, ts, _)
                            if t.op() == o && parent_counts.get(c).unwrap_or(&0) <= &1 =>
                        {
                            children.push(ts.clone());
                        }
                        e => {
                            children
                                .push(Rc::new(PersistentConcatList::Leaf(Rc::new(e.as_term()))));
                        }
                    }
                }
                Entry::NaryTerm(
                    t.op().clone(),
                    Rc::new(PersistentConcatList::Concat(children)),
                    None,
                )
            }
            _ => Entry::Term(Rc::new(term(
                t.op().clone(),
                t.cs()
                    .iter()
                    .map(|c| rewritten.get_mut(c).unwrap().as_term())
                    .collect(),
            ))),
        };
        rewritten.insert(t, entry);
    }
    rewritten.get_mut(&term_).unwrap().as_term()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    fn bool(b: bool) -> Term {
        leaf_term(Op::Const(Value::Bool(b)))
    }

    fn is_flat(t: Term) -> bool {
        PostOrderIter::new(t).all(|c| {
            c.op() == &PF_MUL
                || c.op() == &Op::Tuple
                || c.op().arity().is_some()
                || !c.cs().iter().any(|cc| c.op() == cc.op())
        })
    }

    #[quickcheck]
    fn flatten_random(ArbitraryTerm(t): ArbitraryTerm) -> bool {
        is_flat(flatten_nary_ops(t))
    }

    #[quickcheck]
    fn flatten_semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = flatten_nary_ops(t.clone());
        eval(&t, &vs) == eval(&tt, &vs)
    }

    #[test]
    fn simple_bool() {
        for o in vec![AND, OR, XOR] {
            let t = term![o.clone(); term![o.clone(); bool(true), bool(false)], bool(true)];
            let tt = term![o.clone(); bool(true), bool(false), bool(true)];
            assert_eq!(flatten_nary_ops(t), tt);
        }
    }

    #[test]
    fn simple_bv() {
        for o in vec![BV_AND, BV_OR, BV_XOR, BV_ADD, BV_MUL] {
            let t = term![o.clone(); term![o.clone(); bv_lit(3,5), bv_lit(3,5)], bv_lit(3,5)];
            let tt = term![o.clone(); bv_lit(3, 5), bv_lit(3, 5), bv_lit(3, 5)];
            assert_eq!(flatten_nary_ops(t), tt);
        }
    }
}
