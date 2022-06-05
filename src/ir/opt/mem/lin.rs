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

struct Linearizer;

impl RewritePass for Linearizer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        match &orig.op {
            Op::Const(v @ Value::Array(..)) => Some(leaf_term(Op::Const(super::arr_val_to_tup(v)))),
            Op::Var(_name, s) if super::sort_contains_array(s) => Some(super::array_to_tuple(orig)),
            Op::Call(_name, _arg_names, arg_sorts, ret_sort) => {
                let mut args = rewritten_children();
                for (a, s) in args.iter_mut().zip(arg_sorts) {
                    if super::sort_contains_array(s) {
                        *a = super::resort(a, s)
                    }
                }
                let out = term(orig.op.clone(), args);
                Some(if super::sort_contains_array(ret_sort) {
                    super::array_to_tuple(&out)
                } else {
                    out
                })
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
pub fn linearize(c: &mut Computation) {
    let mut pass = Linearizer;
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
        let before = text::parse_computation(b"
        (computation
          (metadata () () ())
          (let ((z (#a (bv 4) #x0 6 ())))
            (select (ite true (store z #x3 #x1) (store z #x2 #x1)) #x3)
          )
        )",
        );
        let expected = text::parse_computation(
            b"
        (computation
          (metadata () () ())
          (let (
          (z (#t #x0 #x0 #x0 #x0 #x0 #x0))
          )
            ((field 3) (ite true ((update 3) z #x1) ((update 2) z #x1)))
          )
        )",
        );
        let mut after = before.clone();
        linearize(&mut after);
        assert_eq!(after, expected);
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
        linearize(&mut c);
        assert!(array_free(&c.outputs[0]));
        assert_eq!(1, count_ites(&c.outputs[0]));
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
          (metadata () ((A (array (bv 8) (bv 8) 3))) ())
          (let ((tupin (tuple (select A #x00) (select A #x01) (select A #x02))))
            (bvadd ((field 0) tupin) ((field 1) tupin))
          )
        )
        ",
        );
        let mut after = before.clone();
        linearize(&mut after);
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
          (metadata () ((a (bv 8)) (A (array (bv 8) (bv 8) 3))) ())
          (let ((tupin (tuple (select A #x00) (select A #x01) (select A #x02))))
            (bvadd
              ((field 0) tupin)
              ((field 1) tupin)
              (ite (= a #b00000010) ((field 2) tupin) (ite (= a #b00000001) ((field 1) tupin) ((field 0) tupin))))
          )
        )
        ");
        let mut after = before.clone();
        linearize(&mut after);
        assert_eq!(after, expected);
    }

    #[test]
    fn var_tuple_in_array() {
        let before = text::parse_computation(
            b"
        (computation
          (metadata () ((A (array (bv 8) (tuple (bv 8) bool) 3))) ())
          (or ((field 1) (select A #x00))
              (= ((field 0) (select A #x01))
                 ((field 0) (select A #x02))))
        )",
        );
        let expected = text::parse_computation(
            b"
        (computation
          (metadata () ((A (array (bv 8) (tuple (bv 8) bool) 3))) ())
          (let ((tupin
            (tuple
              (tuple ((field 0) (select A #x00)) ((field 1) (select A #x00)))
              (tuple ((field 0) (select A #x01)) ((field 1) (select A #x01)))
              (tuple ((field 0) (select A #x02)) ((field 1) (select A #x02))))))
          (or ((field 1) ((field 0) tupin))
              (= ((field 0) ((field 1) tupin))
                 ((field 0) ((field 2) tupin)))))
        )",
        );
        let mut after = before.clone();
        linearize(&mut after);
        assert_eq!(after, expected);
    }
}
