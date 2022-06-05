//! Memory optimizations

use crate::ir::term::*;

/// Linear-scan array elimination.
///
/// Replace arrays with tuples, using ITEs to handle variable indexing.
pub mod lin;
/// Oblivious array elimination.
///
/// Replace arrays that are accessed at constant indices with tuples.
pub mod obliv;

fn arr_val_to_tup(v: &Value) -> Value {
    match v {
        Value::Array(Array {
            default, map, size, ..
        }) => Value::Tuple({
            let mut vec = vec![arr_val_to_tup(default); *size].into_boxed_slice();
            for (i, v) in map {
                vec[i.as_usize().expect("non usize key")] = arr_val_to_tup(v);
            }
            vec
        }),
        Value::Tuple(xs) => Value::Tuple(xs.iter().map(arr_val_to_tup).collect()),
        v => v.clone(),
    }
}

fn term_arr_val_to_tup(a: Term) -> Term {
    match &a.op {
        Op::Const(v @ Value::Array(..)) => leaf_term(Op::Const(arr_val_to_tup(v))),
        _ => a,
    }
}

/// Read all entries out of an array-containing term and rebuild as a tuple-containing term.
fn array_to_tuple(t: &Term) -> Term {
    match check(t) {
        Sort::Array(..) => term(
            Op::Tuple,
            extras::array_elements(t)
                .map(|c| array_to_tuple(&c))
                .collect(),
        ),
        Sort::Tuple(..) => term(Op::Tuple, extras::tuple_elements(t).map(|c| array_to_tuple(&c)).collect()),
        _ => t.clone(),
    }
}

/// Does this sort contain an array?
fn sort_contains_array(s: &Sort) -> bool {
    match s {
        Sort::Tuple(ss) => ss.iter().any(sort_contains_array),
        Sort::Array(..) => true,
        _ => false,
    }
}

/// Given a sort `s` which may contain array constructors, construct a new sort in which the arrays
/// have been flattened to tuples.
fn array_to_tuple_sort(s: &Sort) -> Sort {
    match s {
        Sort::Tuple(ss) => Sort::Tuple(ss.iter().map(array_to_tuple_sort).collect()),
        Sort::Array(_key, val, sz) => Sort::Tuple(vec![array_to_tuple_sort(val); *sz].into()),
        _ => s.clone(),
    }
}

/// Given a term of tuples, re-shape into sort `s`.
fn resort(t: &Term, s: &Sort) -> Term {
    match s {
        Sort::Array(k, v, sz) => extras::tuple_or_array_elements(t).zip(k.elems_iter()).fold(
            s.default_term(),
            |acc, (t, i)| term![Op::Store; acc, i, resort(&t, v)],
        ),
        Sort::Tuple(ss) => term(
            Op::Tuple,
            extras::tuple_elements(t)
                .zip(ss.iter())
                .map(|(t, s)| resort(&t, s))
                .collect(),
        ),
        _ => t.clone(),
    }
}
