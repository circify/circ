//! Extra algorithms over terms (e.g. substitutions)

use super::*;
use std::cmp::Ordering;

/// Convert `t` to width `w`, though unsigned extension or extraction
pub fn to_width(t: &Term, w: usize) -> Term {
    let old_w = check(t).as_bv();
    match old_w.cmp(&w) {
        Ordering::Less => term(Op::BvUext(w - old_w), vec![t.clone()]),
        Ordering::Equal => t.clone(),
        Ordering::Greater => term(Op::BvExtract(w - 1, 0), vec![t.clone()]),
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
            stack.extend(n.cs().iter().map(|c| (c.clone(), false)));
            continue;
        }
        let new_n = term(
            n.op().clone(),
            n.cs()
                .iter()
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
    let mut c = TermMap::default();
    c.insert(from, to);
    substitute_cache(t, &mut c)
}

/// Is `needle` not in `haystack`?
pub fn does_not_contain(haystack: Term, needle: &Term) -> bool {
    PostOrderIter::new(haystack).all(|descendent| &descendent != needle)
}

/// Is `needle` in `haystack`?
pub fn contains(haystack: Term, needle: &Term) -> bool {
    PostOrderIter::new(haystack).any(|descendent| &descendent == needle)
}

/// Is `v` free in `t`? Wrong in the presence of lets.
pub fn free_in(v: &str, t: Term) -> bool {
    for n in PostOrderIter::new(t) {
        match &n.op() {
            Op::Var(name, _) if v == name => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// Get all the free variables in this term
pub fn free_variables(t: Term) -> FxHashSet<String> {
    PostOrderIter::new(t)
        .filter_map(|n| match &n.op() {
            Op::Var(name, _) => Some(name.into()),
            _ => None,
        })
        .collect()
}

/// Get all the free variables in this term, with sorts
pub fn free_variables_with_sorts(t: Term) -> FxHashSet<(String, Sort)> {
    PostOrderIter::new(t)
        .filter_map(|n| match &n.op() {
            Op::Var(name, sort) => Some((name.into(), sort.clone())),
            _ => None,
        })
        .collect()
}

/// If this term is a constant field or bit-vector, get the unsigned int value.
pub fn as_uint_constant(t: &Term) -> Option<Integer> {
    match &t.op() {
        Op::Const(Value::BitVector(bv)) => Some(bv.uint().clone()),
        Op::Const(Value::Field(f)) => Some(f.i()),
        Op::Const(Value::Bool(b)) => Some((*b).into()),
        _ => None,
    }
}

/// Assert that all variables in the term graph are declared in the metadata.
#[cfg(test)]
pub fn assert_all_vars_declared(c: &Computation) {
    let vars: FxHashSet<String> = c.metadata.vars.iter().map(|p| p.0.clone()).collect();
    for o in &c.outputs {
        for v in free_variables(o.clone()) {
            assert!(vars.contains(&v), "{}", "Variable {v} is not declared");
        }
    }
}

/// Build a map from every term in the computation to its parents.
///
/// Guarantees that every computation term is a key in the map. If there are no
/// parents, the value will be empty.
pub fn parents_map(c: &Computation) -> TermMap<Vec<Term>> {
    let mut parents = TermMap::default();
    for t in c.terms_postorder() {
        parents.insert(t.clone(), Vec::new());
        for c in t.cs() {
            parents.get_mut(c).unwrap().push(t.clone());
        }
    }
    parents
}

/// The elements in this array (select terms) as a vector.
pub fn array_elements(t: &Term) -> Vec<Term> {
    if let Sort::Array(key_sort, _, size) = check(t) {
        key_sort
            .elems_iter()
            .take(size)
            .map(|key| term(Op::Select, vec![t.clone(), key]))
            .collect()
    } else {
        panic!()
    }
}

/// Wrap an array term as a tuple term.
pub fn array_to_tuple(t: &Term) -> Term {
    term(Op::Tuple, array_elements(t))
}

/// Print operator stats
pub fn dump_op_stats() {
    use std::mem::size_of;
    println!("Op size: {}bytes", size_of::<Op>());
    let mut counts: FxHashMap<Op, usize> = FxHashMap::default();
    let mut children: FxHashMap<Op, usize> = FxHashMap::default();
    let add = |map: &mut FxHashMap<Op, usize>, key: &Op, value: usize| {
        if let Some(present_value) = map.get_mut(key) {
            *present_value += value;
        } else {
            map.insert(key.clone(), value);
        }
    };
    hc::Table::for_each(|op, cs| {
        add(&mut counts, op, 1);
        add(&mut children, op, cs.len());
    });
    let mut vector = Vec::new();
    for k in counts.keys() {
        let ct = *counts.get(k).unwrap();
        let cs_ct = *children.get(k).unwrap();
        let ave = cs_ct as f64 / ct as f64;
        vector.push((k.clone(), ct, cs_ct, ave));
    }
    vector.sort_by_key(|t| t.1);
    for (k, ct, cs_ct, ave) in vector {
        let mem = size_of::<Op>() * ct + size_of::<Vec<Term>>() * ct + size_of::<Term>() * cs_ct;
        let s: String = format!("{k}");
        println!("Op {s:>20}, Count {ct:>8}, Children {cs_ct:>8}, Ave {ave:>8.2}, Mem {mem:>20}");
    }
}

/// Iterator over descendents in child-first order.
pub struct PostOrderSkipIter<'a, F: Fn(&Term) -> bool + 'a> {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
    skip_if: &'a F,
}

impl<'a, F: Fn(&Term) -> bool + 'a> PostOrderSkipIter<'a, F> {
    /// Make an iterator over the descendents of `root`.
    pub fn new(root: Term, skip_if: &'a F) -> Self {
        Self {
            stack: vec![(false, root)],
            visited: TermSet::default(),
            skip_if,
        }
    }
}

impl<'a, F: Fn(&Term) -> bool + 'a> std::iter::Iterator for PostOrderSkipIter<'a, F> {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) || (self.skip_if)(t) {
                self.stack.pop();
            } else if !children_pushed {
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs().iter().map(|c| (false, c.clone())));
            } else {
                break;
            }
        }
        self.stack.pop().map(|(_, t)| {
            self.visited.insert(t.clone());
            t
        })
    }
}
