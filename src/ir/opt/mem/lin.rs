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
        v => v.clone(),
    }
}

fn arr_sort_to_tup(v: &Sort) -> Sort {
    match v {
        Sort::Array(_key, value, size) => {
            Sort::Tuple(vec![arr_sort_to_tup(value); *size].into_boxed_slice())
        }
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
        match &orig.op {
            Op::Const(v @ Value::Array(..)) => Some(leaf_term(Op::Const(arr_val_to_tup(v)))),
            Op::Var(name, sort @ Sort::Array(_k, _v, _size)) => {
                let new_value = computation
                    .values
                    .as_ref()
                    .map(|vs| arr_val_to_tup(vs.get(name).unwrap()));
                let vis = computation.metadata.get_input_visibility(name);
                let new_sort = arr_sort_to_tup(sort);
                let new_var_info = vec![(name.clone(), new_sort.clone(), new_value, vis)];
                computation.replace_input(orig.clone(), new_var_info);
                Some(leaf_term(Op::Var(name.clone(), new_sort)))
            }
            Op::Select => {
                let cs = rewritten_children();
                let idx = &cs[1];
                let tup = &cs[0];
                if let Sort::Array(key_sort, _, size) = check(&orig.cs[0]) {
                    assert!(size > 0);
                    let mut fields = (0..size).map(|idx| term![Op::Field(idx); tup.clone()]);
                    let first = fields.next().unwrap();
                    Some(key_sort.elems_iter().take(size).skip(1).zip(fields).fold(first, |acc, (idx_c, field)| {
                        term![Op::Ite; term![Op::Eq; idx.clone(), idx_c], field, acc]
                    }))
                } else {
                    unreachable!()
                }
            }
            Op::Store => {
                let cs = rewritten_children();
                let tup = &cs[0];
                let idx = &cs[1];
                let val = &cs[2];
                if let Sort::Array(key_sort, _, size) = check(&orig.cs[0]) {
                    assert!(size > 0);
                    let mut updates =
                        (0..size).map(|idx| term![Op::Update(idx); tup.clone(), val.clone()]);
                    let first = updates.next().unwrap();
                    Some(key_sort.elems_iter().take(size).skip(1).zip(updates).fold(first, |acc, (idx_c, update)| {
                        term![Op::Ite; term![Op::Eq; idx.clone(), idx_c], update, acc]
                    }))
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
    use crate::ir::term::field::TEST_FIELD;
    use rug::Integer;
    use std::sync::Arc;

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
            .filter(|t| t.op == Op::Ite)
            .count()
    }

    fn field_lit(u: usize) -> Term {
        leaf_term(Op::Const(Value::Field(FieldElem::new(
            Integer::from(u),
            Arc::new(Integer::from(TEST_FIELD)),
        ))))
    }

    #[test]
    fn select_ite_stores() {
        let z = term![Op::Const(Value::Array(Array::new(
            Sort::BitVector(4),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            6
        )))];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), bv_lit(3, 4), bv_lit(1, 4)],
              term![Op::Store; z, bv_lit(2, 4), bv_lit(1, 4)]
            ],
            bv_lit(3, 4)
        ];
        let mut c = Computation::default();
        c.outputs.push(t);
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(5 + 5 + 1 + 5, count_ites(&c.outputs[0]));
    }

    #[test]
    fn select_ite_stores_field() {
        let z = term![Op::Const(Value::Array(Array::new(
            Sort::Field(Arc::new(Integer::from(TEST_FIELD))),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            6
        )))];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), field_lit(3), bv_lit(1, 4)],
              term![Op::Store; z, field_lit(2), bv_lit(1, 4)]
            ],
            field_lit(3)
        ];
        let mut c = Computation::default();
        c.outputs.push(t);
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(5 + 5 + 1 + 5, count_ites(&c.outputs[0]));
    }
}
