//! Contains a number of constant terms for testing
#![allow(missing_docs)]

use super::*;
use fxhash::FxHashMap;

#[test]
fn eq() {
    let v = leaf_term(Op::Var("a".to_owned(), Sort::Bool));
    let u = leaf_term(Op::Var("a".to_owned(), Sort::Bool));
    let w = leaf_term(Op::Var("b".to_owned(), Sort::Bool));
    assert_eq!(v, u);
    assert!(v != w);
    assert!(u != w);
}

#[test]
fn bv2pf() {
    assert_eq!(
        leaf_term(Op::Const(eval(
            &text::parse_term(b"(bvshl #b0001 #b0010)"),
            &FxHashMap::default()
        ))),
        text::parse_term(b" #b0100 ")
    );
    assert_eq!(
        leaf_term(Op::Const(eval(
            &text::parse_term(b" (set_default_modulus 17 ((pf2bv 4) #f1)) "),
            &FxHashMap::default()
        ))),
        text::parse_term(b" #b0001 ")
    );
}

#[test]
fn map_test_bool_key() {
    let a1 = make_array(Sort::Bool, Sort::Bool, vec![bool(true), bool(true)]);
    let a2 = make_array(Sort::Bool, Sort::Bool, vec![bool(true), bool(false)]);
    let actual = term![Op::Map(Box::new(Op::Eq)); a1, a2];
    let expected = make_array(Sort::Bool, Sort::Bool, vec![bool(true), bool(false)]);
    assert_eq!(
        eval(&actual, &FxHashMap::default()),
        eval(&expected, &FxHashMap::default())
    );
}

#[test]
fn map_test_bv_key() {
    let a1 = make_array(
        Sort::BitVector(32),
        Sort::Bool,
        vec![bool(true), bool(true), bool(false), bool(false)],
    );
    let a2 = make_array(
        Sort::BitVector(32),
        Sort::Bool,
        vec![bool(true), bool(false), bool(true), bool(false)],
    );
    let actual = term![Op::Map(Box::new(Op::Eq)); a1, a2];
    let expected = make_array(
        Sort::BitVector(32),
        Sort::Bool,
        vec![bool(true), bool(false), bool(false), bool(true)],
    );
    assert_eq!(
        eval(&actual, &FxHashMap::default()),
        eval(&expected, &FxHashMap::default())
    );

    let a1 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0001, 4),
            bv_lit(0b0010, 4),
            bv_lit(0b0011, 4),
            bv_lit(0b0100, 4),
        ],
    );
    let a2 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0001, 4),
            bv_lit(0b0100, 4),
            bv_lit(0b1001, 4),
            bv_lit(0b0000, 4),
        ],
    );
    let actual_eq = term![Op::Map(Box::new(Op::Eq)); a1.clone(), a2.clone()];
    let actual_add = term![Op::Map(Box::new(BV_ADD)); a1, a2];
    let expected_eq = make_array(
        Sort::BitVector(32),
        Sort::Bool,
        vec![bool(true), bool(false), bool(false), bool(false)],
    );
    let expected_add = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0010, 4),
            bv_lit(0b0110, 4),
            bv_lit(0b1100, 4),
            bv_lit(0b0100, 4),
        ],
    );

    assert_eq!(
        eval(&actual_eq, &FxHashMap::default()),
        eval(&expected_eq, &FxHashMap::default())
    );
    assert_eq!(
        eval(&actual_add, &FxHashMap::default()),
        eval(&expected_add, &FxHashMap::default())
    );
}

#[test]
fn test_rot() {
    let a = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0001, 4),
            bv_lit(0b0010, 4),
            bv_lit(0b0011, 4),
            bv_lit(0b0100, 4),
        ],
    );
    let expected_rot_0 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0001, 4),
            bv_lit(0b0010, 4),
            bv_lit(0b0011, 4),
            bv_lit(0b0100, 4),
        ],
    );
    let expected_rot_1 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0100, 4),
            bv_lit(0b0001, 4),
            bv_lit(0b0010, 4),
            bv_lit(0b0011, 4),
        ],
    );
    let expected_rot_2 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![
            bv_lit(0b0011, 4),
            bv_lit(0b0100, 4),
            bv_lit(0b0001, 4),
            bv_lit(0b0010, 4),
        ],
    );

    let rot_0 = term![Op::Rot(0); a.clone()];
    let rot_1 = term![Op::Rot(1); a.clone()];
    let rot_2 = term![Op::Rot(2); a];

    assert_eq!(
        eval(&rot_0, &FxHashMap::default()),
        eval(&expected_rot_0, &FxHashMap::default())
    );
    assert_eq!(
        eval(&rot_1, &FxHashMap::default()),
        eval(&expected_rot_1, &FxHashMap::default())
    );
    assert_eq!(
        eval(&rot_2, &FxHashMap::default()),
        eval(&expected_rot_2, &FxHashMap::default())
    );
}

mod type_ {
    use super::*;

    fn t() -> Term {
        let v = leaf_term(Op::Var("b".to_owned(), Sort::BitVector(4)));
        term![
            Op::BvBit(4);
            term![
                Op::BvConcat;
                v,
                term![Op::BoolToBv; leaf_term(Op::Var("c".to_owned(), Sort::Bool))]
            ]
        ]
    }

    #[test]
    fn vars() {
        let v = leaf_term(Op::Var("a".to_owned(), Sort::Bool));
        assert_eq!(check(&v), Sort::Bool);
        let v = leaf_term(Op::Var("b".to_owned(), Sort::BitVector(4)));
        assert_eq!(check(&v), Sort::BitVector(4));
        let v = t();
        assert_eq!(check(&v), Sort::Bool);
    }

    #[test]
    fn traversal() {
        let tt = t();
        assert_eq!(
            vec![
                Op::Var("c".to_owned(), Sort::Bool),
                Op::BoolToBv,
                Op::Var("b".to_owned(), Sort::BitVector(4)),
                Op::BvConcat,
                Op::BvBit(4),
            ],
            PostOrderIter::new(tt)
                .map(|t| t.op().clone())
                .collect::<Vec<_>>()
        );
    }
}

fn bool(b: bool) -> Term {
    leaf_term(Op::Const(Value::Bool(b)))
}

pub fn bool_and_tests() -> Vec<Term> {
    vec![term![
        Op::Eq;
        term![AND; bool(true), bool(false)],
        bool(false)
    ]]
}

pub fn bv_eq_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            bv_lit(0b1111, 4),
            bv_lit(0b1111, 4)
        ],
        term![
            Op::Eq;
            bv_lit(0b0101, 4),
            bv_lit(0b0101, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::Eq;
                bv_lit(0b0101, 4),
                bv_lit(0b0101, 4)
            ],
            bool(true)
        ],
        term![
            Op::Eq;
            term![
                Op::Eq;
                bv_lit(0b0101, 4),
                bv_lit(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_le_tests() -> Vec<Term> {
    vec![
        term![
            BV_ULE;
            bv_lit(0b1111, 4),
            bv_lit(0b1111, 4)
        ],
        term![
            BV_ULE;
            bv_lit(0b0101, 4),
            bv_lit(0b0101, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_ULE;
                bv_lit(0b0101, 4),
                bv_lit(0b0101, 4)
            ],
            bool(true)
        ],
        term![
            Op::Eq;
            term![
                BV_ULE;
                bv_lit(0b1101, 4),
                bv_lit(0b0101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_sle_tests() -> Vec<Term> {
    vec![
        term![
            BV_SLE;
            bv_lit(0b1111, 4),
            bv_lit(0b1111, 4)
        ],
        term![
            BV_SLE;
            bv_lit(0b1000, 4),
            bv_lit(0b0111, 4)
        ],
        term![
            BV_SLE;
            bv_lit(0b1000, 4),
            bv_lit(0b0000, 4)
        ],
        term![
            BV_SLE;
            bv_lit(0b1111, 4),
            bv_lit(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_SLE;
                bv_lit(0b0101, 4),
                bv_lit(0b0101, 4)
            ],
            bool(true)
        ],
        term![
            Op::Eq;
            term![
                BV_SLE;
                bv_lit(0b0101, 4),
                bv_lit(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_slt_tests() -> Vec<Term> {
    vec![
        term![
            BV_SLT;
            bv_lit(0b0000, 4),
            bv_lit(0b0001, 4)
        ],
        term![
            BV_SLT;
            bv_lit(0b1111, 4),
            bv_lit(0b0000, 4)
        ],
        term![
            BV_SLT;
            bv_lit(0b0101, 4),
            bv_lit(0b0110, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_SLT;
                bv_lit(0b0101, 4),
                bv_lit(0b0101, 4)
            ],
            bool(false)
        ],
        term![
            Op::Eq;
            term![
                BV_SLT;
                bv_lit(0b0101, 4),
                bv_lit(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_concat_tests() -> Vec<Term> {
    vec![term![
        Op::Eq;
        term![
            BV_CONCAT;
            bv_lit(0b0101, 4),
            bv_lit(0b0100, 4)
        ],
        bv_lit(0b01010100, 8)
    ]]
}

pub fn bv_not_tests() -> Vec<Term> {
    vec![term![
        Op::Eq;
        term![
            BV_NOT;
            bv_lit(0b0100, 4)
        ],
        bv_lit(0b1011, 4)
    ]]
}

pub fn bv_neg_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![
                BV_NEG;
                bv_lit(0b0100, 4)
            ],
            bv_lit(0b1100, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_NEG;
                bv_lit(0b0000, 4)
            ],
            bv_lit(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_NEG;
                bv_lit(0b1111, 4)
            ],
            bv_lit(0b0001, 4)
        ],
    ]
}

pub fn bv_lt_tests() -> Vec<Term> {
    vec![
        term![
            BV_ULT;
            bv_lit(0b0111, 4),
            bv_lit(0b1111, 4)
        ],
        term![
            BV_ULT;
            bv_lit(0b0101, 4),
            bv_lit(0b1101, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_ULT;
                bv_lit(0b0101, 4),
                bv_lit(0b0101, 4)
            ],
            bool(false)
        ],
        term![
            Op::Eq;
            term![
                BV_ULT;
                bv_lit(0b0101, 4),
                bv_lit(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_and_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_AND; bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b1111, 4)
        ],
        term![
            Op::Eq;
            term![BV_AND; bv_lit(0b0111,4), bv_lit(0b1101,4)],
            bv_lit(0b0101, 4)
        ],
    ]
}
pub fn bv_or_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_OR; bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b1111, 4)
        ],
        term![
            Op::Eq;
            term![BV_OR; bv_lit(0b0111,4), bv_lit(0b0101,4)],
            bv_lit(0b0111, 4)
        ],
    ]
}
pub fn bv_add_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_ADD; bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b1110, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv_lit(0b1111,4), bv_lit(0b0101,4)],
            bv_lit(0b0100, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv_lit(0b1111,4), bv_lit(0b1111,4), bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b1100, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv_lit(0b1111,4), bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b1101, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv_lit(0b0000,4), bv_lit(0b1110,4), bv_lit(0b0000,4), bv_lit(0b0000,4)],
            bv_lit(0b1110, 4)
        ],
    ]
}
pub fn bv_mul_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_MUL; bv_lit(0b0001,4)],
            bv_lit(0b0001, 4)
        ],
        term![
            Op::Eq;
            term![BV_MUL; bv_lit(0b0000,4), bv_lit(0b1111,4)],
            bv_lit(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![BV_MUL; bv_lit(0b0010,4), bv_lit(0b1111,4)],
            bv_lit(0b1110, 4)
        ],
        term![
            Op::Eq;
            term![BV_MUL; bv_lit(0b1001,4), bv_lit(0b0101,4)],
            bv_lit(0b1101, 4)
        ],
    ]
}

pub fn bv_sext_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![
                Op::BvSext(2);
                bv_lit(0b10, 2)
            ],
            bv_lit(0b1110, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvSext(2);
                bv_lit(0b01, 2)
            ],
            bv_lit(0b0001, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvSext(2);
                term![BV_ADD; bv_lit(0b01, 2), bv_lit(0b01, 2)]
            ],
            bv_lit(0b1110, 4)
        ],
    ]
}

pub fn bv_uext_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![
                Op::BvUext(2);
                bv_lit(0b10, 2)
            ],
            bv_lit(0b0010, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvUext(2);
                term![BV_ADD; bv_lit(0b01, 2), bv_lit(0b01, 2)]
            ],
            bv_lit(0b0010, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvUext(2);
                bv_lit(0b01, 2)
            ],
            bv_lit(0b0001, 4)
        ],
    ]
}
pub fn bv_sub_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_SUB; bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![BV_SUB; bv_lit(0b1111,4), bv_lit(0b0000,4)],
            bv_lit(0b1111, 4)
        ],
        term![
            Op::Eq;
            term![BV_SUB; bv_lit(0b1111,4), bv_lit(0b1110,4)],
            bv_lit(0b0001, 4)
        ],
        term![
            Op::Eq;
            term![BV_SUB; bv_lit(0b0000,4), bv_lit(0b1111,4)],
            bv_lit(0b0001, 4)
        ],
    ]
}

#[test]
fn pf2bool_eval() {
    let t = text::parse_term(b"(declare () (pf2bool_trusted (ite false #f1m11 #f0m11)))");
    let actual_output = eval(&t, &Default::default());
    let expected_output = text::parse_value_map(b"(let ((output false)) false)");
    assert_eq!(&actual_output, expected_output.get("output").unwrap());
}
