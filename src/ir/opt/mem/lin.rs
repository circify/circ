//! Linear Memory implementation.
//!
//! The idea is to replace each array with a tuple, and use ITEs to account for variable indexing.
use super::super::visit::RewritePass;
use crate::ir::term::*;

struct Linearizer;

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
        Value::Tuple(vs) => Value::Tuple(
            vs.iter()
                .map(arr_val_to_tup)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
        v => v.clone(),
    }
}

impl RewritePass for Linearizer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        match &orig.op() {
            Op::Const(v) => Some(const_(arr_val_to_tup(v))),
            Op::Var(v) if v.sort.is_array() => {
                let precomp = extras::array_to_tuple(orig);
                let new_name = format!("{}.tup", v.name);
                let new_sort = check(&precomp);
                computation.extend_precomputation(new_name.clone(), precomp);
                Some(var(new_name, new_sort))
            }
            Op::Array(..) => Some(term(Op::Tuple, rewritten_children())),
            Op::Fill(f) => Some(term(
                Op::Tuple,
                vec![rewritten_children().pop().unwrap(); f.size],
            )),
            Op::Select => {
                let cs = rewritten_children();
                let idx = &cs[1];
                let tup = &cs[0];
                if let Sort::Array(a) = check(&orig.cs()[0]) {
                    assert!(a.size > 0);
                    if idx.is_const() {
                        Some(
                            extras::as_uint_constant(idx)
                                .and_then(|cidx| cidx.to_usize())
                                .and_then(|u| {
                                    (u < a.size).then_some(term![Op::Field(u); tup.clone()])
                                })
                                .unwrap_or_else(|| a.val.default_term()),
                        )
                    } else {
                        let value_sort = check(tup).as_tuple()[0].clone();
                        if value_sort.is_group() {
                            // if values are a group
                            // then emit v0 + ite(idx == i1, v1 - v0, 0) + ... it(idx = iN, vN - v0, 0)
                            // where  +, -, 0 are defined by the group.
                            //
                            // we do this because if the values are constant, then the above sum is
                            // linear, which is very nice for most backends.
                            let mut fields =
                                (0..a.size).map(|idx| term![Op::Field(idx); tup.clone()]);
                            let first = fields.next().unwrap();
                            let zero = value_sort.group_identity();
                            Some(
                                value_sort.group_add_nary(
                                    std::iter::once(first.clone())
                                        .chain(
                                            a.key
                                                .elems_iter()
                                                .take(a.size)
                                                .skip(1)
                                                .zip(fields)
                                                .map(|(idx_c, field)| {
                                                    term![Op::Ite;
                                                        term![Op::Eq; idx.clone(), idx_c],
                                                        value_sort.group_sub(field, first.clone()),
                                                        zero.clone()
                                                    ]
                                                }),
                                        )
                                        .collect(),
                                ),
                            )
                        } else {
                            // otherwise, ite(idx == iN, vN, ... ite(idx == i1, v1, v0) ... )
                            let mut fields =
                                (0..a.size).map(|idx| term![Op::Field(idx); tup.clone()]);
                            let first = fields.next().unwrap();
                            Some(a.key.elems_iter().take(a.size).skip(1).zip(fields).fold(first, |acc, (idx_c, field)| {
                                term![Op::Ite; term![Op::Eq; idx.clone(), idx_c], field, acc]
                            }))
                        }
                    }
                } else {
                    unreachable!()
                }
            }
            Op::Store => {
                let cs = rewritten_children();
                let tup = &cs[0];
                let idx = &cs[1];
                let val = &cs[2];
                if let Sort::Array(a) = check(&orig.cs()[0]) {
                    assert!(a.size > 0);
                    if idx.is_const() {
                        Some(
                            extras::as_uint_constant(idx)
                                .and_then(|cidx| cidx.to_usize())
                                .and_then(|u| {
                                    (u < a.size)
                                        .then_some(term![Op::Update(u); tup.clone(), val.clone()])
                                })
                                .unwrap_or_else(|| tup.clone()),
                        )
                    } else {
                        let mut updates =
                            (0..a.size).map(|idx| term![Op::Update(idx); tup.clone(), val.clone()]);
                        let first = updates.next().unwrap();
                        Some(a.key.elems_iter().take(a.size).skip(1).zip(updates).fold(first, |acc, (idx_c, update)| {
                        term![Op::Ite; term![Op::Eq; idx.clone(), idx_c], update, acc]
                    }))
                    }
                } else {
                    unreachable!()
                }
            }
            Op::CStore => {
                let cs = rewritten_children();
                let tup = &cs[0];
                let idx = &cs[1];
                let val = &cs[2];
                let cond = &cs[3];
                if let Sort::Array(a) = check(&orig.cs()[0]) {
                    assert!(a.size > 0);
                    if idx.is_const() {
                        Some(
                            extras::as_uint_constant(idx)
                                .and_then(|cidx| cidx.to_usize())
                                .and_then(|u| {
                                    (u < a.size)
                                        .then_some(term![Op::Ite; cond.clone(), term![Op::Update(u); tup.clone(), val.clone()], tup.clone()])
                                })
                                .unwrap_or_else(|| tup.clone()),
                        )
                    } else {
                        let mut updates =
                            (0..a.size).map(|idx| term![Op::Update(idx); tup.clone(), val.clone()]);
                        let first = updates.next().unwrap();
                        Some(a.key.elems_iter().take(a.size).skip(1).zip(updates).fold(first, |acc, (idx_c, update)| {
                        term![Op::Ite; term![AND; term![Op::Eq; idx.clone(), idx_c], cond.clone()], update, acc]
                    }))
                    }
                } else {
                    unreachable!()
                }
            }
            // ITEs and EQs are correctly rewritten by default.
            _ => None,
        }
    }
}

/// Eliminate arrays using linear scans. See module documentation.
pub fn linearize(c: &mut Computation) {
    let mut pass = Linearizer;
    pass.traverse(c);
}

#[cfg(test)]
mod test {
    use super::*;

    fn array_free(t: &Term) -> bool {
        for c in PostOrderIter::new(t.clone()) {
            if let Sort::Array(..) = check(&c) {
                return false;
            }
        }
        true
    }

    fn count_ites(t: &Term) -> usize {
        PostOrderIter::new(t.clone())
            .filter(|t| t.op() == &Op::Ite)
            .count()
    }

    #[test]
    fn select_ite_stores() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs (a (bv 4)) (b (bv 4)) (c (bv 4))) (commitments))
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (bv 4) #x0 4 ()))
                        (store_1 (store c_array a #x1))
                        (store_2 (store c_array b #x2))
                    )
                    (select (ite true store_1 store_2) c)
                )
            )
        ",
        );
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(3 + 3 + 1 + 3, count_ites(&c.outputs[0]));
    }

    #[test]
    fn select_ite_stores_field() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs (a (mod 5)) (b (mod 5)) (c (mod 5))) (commitments))
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (mod 5) #f1m5 4 ()))
                        (store_1 (store c_array a #f1m5))
                        (store_2 (store c_array b #f2m5))
                    )
                    (select (ite true store_1 store_2) c)
                )
            )
        ",
        );
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(3 + 3 + 1 + 3, count_ites(&c.outputs[0]));
    }

    #[test]
    fn select_ite_stores_const() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs (a (bv 4)) (b (bv 4)) (c (bv 4))) (commitments))
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (bv 4) #x0 4 ()))
                        (store_1 (store c_array #x0 #x1))
                        (store_2 (store c_array b #x2))
                    )
                    (select (ite true store_1 store_2) c)
                )
            )
        ",
        );
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(3 + 1 + 3, count_ites(&c.outputs[0]));
    }

    #[test]
    fn select_ite_stores_field_const() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs (a (mod 5)) (b (mod 5)) (c (mod 5))) (commitments))
                (precompute () () (#t ))
                (let
                    (
                        (c_array (#a (mod 5) #f1m5 4 ()))
                        (store_1 (store c_array #f1m5 #f1m5))
                        (store_2 (store c_array b #f2m5))
                    )
                    (select (ite true store_1 store_2) c)
                )
            )
        ",
        );
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(3 + 1 + 3, count_ites(&c.outputs[0]));
    }
}
