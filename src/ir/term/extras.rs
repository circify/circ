//! Extra algorithms over terms (e.g. substitutions)

use super::*;
use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};

/// Convert `t` to width `w`, though unsigned extension or extraction
pub fn to_width(t: &Term, w: usize) -> Term {
    let old_w = check(t).as_bv();
    match old_w.cmp(&w) {
        Ordering::Less => term(Op::BvUext(w - old_w), vec![t.clone()]),
        Ordering::Equal => t.clone(),
        Ordering::Greater => term(Op::BvExtract(w - 1, 0), vec![t.clone()]),
    }
}

/// A wrapper for `Term`, which displays the term in a letified fashion, so that no term is
/// duplicated.
///
/// This is a pretty stupid implementation. It replaces every term.
pub struct Letified(pub Term);

impl Display for Letified {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        //let parent_count = {
        //    let mut parent_count = HashMap::default();
        //    for t in PostOrderIter::new(self.0.clone()) {
        //        for c in &t.cs {
        //            let mut parents = parent_count.entry(&c).or_insert_with(|| 0);
        //            *parents += 1;
        //        }
        //    }
        //    parent_count
        //};
        let mut let_ct = 0;
        let mut print_as = TermMap::new();

        let mut parent_counts = TermMap::<usize>::new();
        for t in PostOrderIter::new(self.0.clone()) {
            for c in t.cs.iter().cloned() {
                *parent_counts.entry(c).or_insert(0) += 1;
            }
        }

        writeln!(f, "(let (")?;
        for t in PostOrderIter::new(self.0.clone()) {
            if parent_counts.get(&t).unwrap_or(&0) > &1 && !t.cs.is_empty() {
                let name = format!("let_{}", let_ct);
                let_ct += 1;
                let sort = check(&t);
                write!(f, "  ({} ", name)?;
                let var = leaf_term(Op::Var(name, sort));
                writeln!(f, "{})", substitute_cache(&t, &mut print_as))?;
                print_as.insert(t, var);
            }
        }
        writeln!(f, ") {})", substitute_cache(&self.0, &mut print_as))
    }
}

/// Rewrites `t`, applying the substitutions in `subs`.
///
/// The substitution map is taken mutably; this function will add rewrites to it.
/// This allows the same map to be re-used across multiple rewrites, with caching.
///
/// TODO: Return a reference into the subs.
pub fn substitute_cache(t: &Term, subs: &mut TermMap<Term>) -> Term {
    let mut stack = vec![(t.clone(), false)];

    // Maps terms to their rewritten versions.
    while let Some((n, children_pushed)) = stack.pop() {
        if subs.contains_key(&n) {
            continue;
        }
        if !children_pushed {
            stack.push((n.clone(), true));
            stack.extend(n.cs.iter().map(|c| (c.clone(), false)));
            continue;
        }
        let new_n = term(
            n.op.clone(),
            n.cs.iter()
                .map(|c| subs.get(c).expect("postorder").clone())
                .collect(),
        );
        subs.insert(n.clone(), new_n);
    }
    subs.get(t).expect("postorder").clone()
}

/// Rewrites `t`, applying the substitutions in `subs`.
///
/// The substitution map is taken mutably; this function will add rewrites to it.
/// This allows the same map to be re-used across multiple rewrites, with caching.
pub fn substitute(t: &Term, mut subs: TermMap<Term>) -> Term {
    substitute_cache(t, &mut subs)
}

/// Rewrites `t`, applying `from -> to`.
///
/// The substitution map is taken mutably; this function will add rewrites to it.
/// This allows the same map to be re-used across multiple rewrites, with caching.
pub fn substitute_single(t: &Term, from: Term, to: Term) -> Term {
    let mut c = TermMap::new();
    c.insert(from, to);
    substitute_cache(t, &mut c)
}

/// Is `needle` not in `haystack`?
pub fn does_not_contain(haystack: Term, needle: &Term) -> bool {
    PostOrderIter::new(haystack)
        .into_iter()
        .all(|descendent| &descendent != needle)
}

/// Is `needle` in `haystack`?
pub fn contains(haystack: Term, needle: &Term) -> bool {
    PostOrderIter::new(haystack)
        .into_iter()
        .any(|descendent| &descendent == needle)
}

/// Is `v` free in `t`? Wrong in the presence of lets.
pub fn free_in(v: &str, t: Term) -> bool {
    for n in PostOrderIter::new(t) {
        match &n.op {
            Op::Var(name, _) if v == name => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// If this term is a constant field or bit-vector, get the unsigned int value.
pub fn as_uint_constant(t: &Term) -> Option<Integer> {
    match &t.op {
        Op::Const(Value::BitVector(bv)) => Some(bv.uint().clone()),
        Op::Const(Value::Field(f)) => Some(f.i()),
        _ => None,
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::term;

    fn remove_whitespace(a: &str) -> String {
        let mut aa = a.to_owned();
        aa.retain(|c| !c.is_whitespace());
        aa
    }

    #[test]
    fn letified_no_dups() {
        let t = term![Op::Eq; term![Op::BvNaryOp(BvNaryOp::Add); bv_lit(4,3), bv_lit(1,3)], bv_lit(5,3)];
        assert_eq!(
            remove_whitespace("(let ()(= (bvadd #b100 #b001) #b101))"),
            remove_whitespace(&format!("{}", Letified(t))),
        );
    }
    #[test]
    fn letified_1_dup() {
        let a = term![Op::BvNaryOp(BvNaryOp::Add); bv_lit(4,3), bv_lit(1,3)];
        let t = term![Op::Eq; a.clone(), a];
        assert_eq!(
            remove_whitespace("(let ((let_0 (bvadd #b100 #b001)))(= let_0 let_0))"),
            remove_whitespace(&format!("{}", Letified(t))),
        );
    }
}
