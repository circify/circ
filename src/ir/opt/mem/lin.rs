//! Linear Memory implementation.
//!
//! The idea is to replace each array with a tuple, and use ITEs to account for variable indexing.
//!
//! At a sort level, the following rewrites are performed:
//!
//!    * lowercase letters denote un-rewritten entities, and uppercase letter
//!      denote post-rewrite entities.
//!    * `(tuple s1 ... sn)` -> `(tuple S1 ... Sn)`
//!    * `(array k v N)` -> `(tuple (repeat N V))`
//!    * `s` -> `s`
//!
//! Notes about different classes of terms:
//!
//!    * variables: arrays are *fully read* and re-assembled as tuples
//!      * the original variable is *not modified*
//!    * function outputs: same as variables
//!    * values: are re-built
//!    * function inputs: un-modified
//! 
use super::super::visit::RewritePass;
use crate::ir::term::*;

struct Linearizer {
    is_entry: bool,
}

impl RewritePass for Linearizer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        match &orig.op {
            Op::Const(v @ Value::Array(..)) => Some(leaf_term(Op::Const(super::arr_val_to_tup(v)))),
            Op::Var(name, s) if super::sort_contains_array(s) => {
                let precomp = super::array_to_tuple(orig);
                let new_name = format!("{}.tup", name);
                let new_sort = check(&precomp);
                if self.is_entry {
                    computation.extend_precomputation(new_name.clone(), precomp);
                } else {
                    let vis = computation.metadata.get_input_visibility(name);
                    computation.remove_var(name);
                    computation.new_var(&new_name, new_sort.clone(), vis, None);
                }
                let new_term = leaf_term(Op::Var(new_name, new_sort));
                Some(new_term)
            }
            Op::Call(name, arg_names, arg_sorts, ret_sort) => {
                let (new_arg_names, new_arg_sorts): (Vec<String>, Vec<Sort>) = arg_names
                    .into_iter()
                    .zip(arg_sorts)
                    .map(|(name, sort)| {
                        if super::sort_contains_array(sort) {
                            (
                                format!("{}.tup", name),
                                super::array_to_tuple_sort(sort),
                            )
                        } else {
                            (name.clone(), sort.clone())
                        }
                    })
                    .unzip();

                Some(term(
                    Op::Call(
                        name.clone(),
                        new_arg_names,
                        new_arg_sorts,
                        super::array_to_tuple_sort(ret_sort),
                    ),
                    rewritten_children(),
                ))
            }
            Op::Select => {
                let cs = rewritten_children();
                let idx = &cs[1];
                let tup = &cs[0];
                if let Sort::Array(key_sort, _, size) = check(&orig.cs[0]) {
                    assert!(size > 0);
                    if idx.is_const() {
                        let idx_usize = extras::as_uint_constant(idx)
                            .expect("non-integer constant")
                            .to_usize()
                            .expect("non-usize constant");
                        Some(term![Op::Field(idx_usize); tup.clone()])
                    } else {
                        let mut fields = (0..size).map(|idx| term![Op::Field(idx); tup.clone()]);
                        let first = fields.next().unwrap();
                        Some(key_sort.elems_iter().take(size).skip(1).zip(fields).fold(first, |acc, (idx_c, field)| {
                            term![Op::Ite; term![Op::Eq; idx.clone(), idx_c], field, acc]
                        }))
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
                if let Sort::Array(key_sort, _, size) = check(&orig.cs[0]) {
                    assert!(size > 0);
                    if idx.is_const() {
                        let idx_usize = extras::as_uint_constant(idx)
                            .expect("non-integer constant")
                            .to_usize()
                            .expect("non-usize constant");
                        Some(term![Op::Update(idx_usize); tup.clone(), val.clone()])
                    } else {
                        let mut updates =
                            (0..size).map(|idx| term![Op::Update(idx); tup.clone(), val.clone()]);
                        let first = updates.next().unwrap();
                        Some(key_sort.elems_iter().take(size).skip(1).zip(updates).fold(first, |acc, (idx_c, update)| {
                            term![Op::Ite; term![Op::Eq; idx.clone(), idx_c], update, acc]
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
pub fn linearize(c: &mut Computation, is_entry: bool) {
    let mut pass = Linearizer { is_entry };
    pass.traverse(c);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::field::DFL_T;

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
        leaf_term(Op::Const(Value::Field(DFL_T.new_v(u))))
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
        linearize(&mut c, true);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(5 + 5 + 1 + 5, count_ites(&c.outputs[0]));
    }

    #[test]
    fn select_ite_stores_field() {
        let z = term![Op::Const(Value::Array(Array::new(
            Sort::Field(DFL_T.clone()),
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
        linearize(&mut c, true);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(5 + 5 + 1 + 5, count_ites(&c.outputs[0]));
    }

    #[test]
    fn oblivious() {
        let before = text::parse_computation(
            b"
        (computation
          (metadata () ((A (array (bv 8) (bv 8) 3))) ())
          (bvadd (select A #x00) (select A #x01))
        )
        ",
        );
        let expected = text::parse_computation(
            b"
        (computation
          (metadata () ((A.tup (tuple (bv 8) (bv 8) (bv 8)))) ())
          (bvadd ((field 0) A.tup) ((field 1) A.tup))
        )
        ",
        );
        let mut after = before.clone();
        linearize(&mut after, false);
        assert_eq!(after, expected);
    }

    #[test]
    fn semi_oblivious() {
        let before = text::parse_computation(
            b"
        (computation
          (metadata () ((a (bv 8)) (A (array (bv 8) (bv 8) 3))) ())
          (bvadd (select A #x00) (select A #x01) (select A a))
        )
        ",
        );
        let expected = text::parse_computation(b"
        (computation
          (metadata () ((a (bv 8)) (A.tup (tuple (bv 8) (bv 8) (bv 8)))) ())
          (bvadd
            ((field 0) A.tup)
            ((field 1) A.tup)
            (ite (= a #b00000010) ((field 2) A.tup) (ite (= a #b00000001) ((field 1) A.tup) ((field 0) A.tup))))
        )
        ");
        let mut after = before.clone();
        linearize(&mut after, false);
        assert_eq!(after, expected);
    }
}
