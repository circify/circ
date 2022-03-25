//! Contains a number of constant terms for testing
#![allow(missing_docs)]

use super::*;
use crate::target::r1cs::trans::test::bv;
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
fn map_eq_test() {
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
    let t = term![Op::Map(Box::new(Op::Eq)); a1, a2];

    let val = eval(&t, &FxHashMap::default());
    println!("Value is: {}", val);

    let a1 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![bv(0b0001, 4), bv(0b0010, 4), bv(0b0011, 4), bv(0b0100, 4)],
    );

    let a2 = make_array(
        Sort::BitVector(32),
        Sort::BitVector(4),
        vec![bv(0b0001, 4), bv(0b0100, 4), bv(0b1001, 4), bv(0b0000, 4)],
    );

    let t_eq = term![Op::Map(Box::new(Op::Eq)); a1.clone(), a2.clone()];
    let t_add = term![Op::Map(Box::new(BV_ADD)); a1.clone(), a2.clone()];

    println!("MAP EQ  Value is: {}", eval(&t_eq, &FxHashMap::default()));
    println!("MAP ADD Value is: {}", eval(&t_add, &FxHashMap::default()))
    //let res = get_value(t)
    //let ans = true
    //assert true
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
                .map(|t| t.op.clone())
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
            bv(0b1111, 4),
            bv(0b1111, 4)
        ],
        term![
            Op::Eq;
            bv(0b0101, 4),
            bv(0b0101, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::Eq;
                bv(0b0101, 4),
                bv(0b0101, 4)
            ],
            bool(true)
        ],
        term![
            Op::Eq;
            term![
                Op::Eq;
                bv(0b0101, 4),
                bv(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_le_tests() -> Vec<Term> {
    vec![
        term![
            BV_ULE;
            bv(0b1111, 4),
            bv(0b1111, 4)
        ],
        term![
            BV_ULE;
            bv(0b0101, 4),
            bv(0b0101, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_ULE;
                bv(0b0101, 4),
                bv(0b0101, 4)
            ],
            bool(true)
        ],
        term![
            Op::Eq;
            term![
                BV_ULE;
                bv(0b1101, 4),
                bv(0b0101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_sle_tests() -> Vec<Term> {
    vec![
        term![
            BV_SLE;
            bv(0b1111, 4),
            bv(0b1111, 4)
        ],
        term![
            BV_SLE;
            bv(0b1000, 4),
            bv(0b0111, 4)
        ],
        term![
            BV_SLE;
            bv(0b1000, 4),
            bv(0b0000, 4)
        ],
        term![
            BV_SLE;
            bv(0b1111, 4),
            bv(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_SLE;
                bv(0b0101, 4),
                bv(0b0101, 4)
            ],
            bool(true)
        ],
        term![
            Op::Eq;
            term![
                BV_SLE;
                bv(0b0101, 4),
                bv(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_slt_tests() -> Vec<Term> {
    vec![
        term![
            BV_SLT;
            bv(0b0000, 4),
            bv(0b0001, 4)
        ],
        term![
            BV_SLT;
            bv(0b1111, 4),
            bv(0b0000, 4)
        ],
        term![
            BV_SLT;
            bv(0b0101, 4),
            bv(0b0110, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_SLT;
                bv(0b0101, 4),
                bv(0b0101, 4)
            ],
            bool(false)
        ],
        term![
            Op::Eq;
            term![
                BV_SLT;
                bv(0b0101, 4),
                bv(0b1101, 4)
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
            bv(0b0101, 4),
            bv(0b0100, 4)
        ],
        bv(0b01010100, 8)
    ]]
}

pub fn bv_not_tests() -> Vec<Term> {
    vec![term![
        Op::Eq;
        term![
            BV_NOT;
            bv(0b0100, 4)
        ],
        bv(0b1011, 4)
    ]]
}

pub fn bv_neg_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![
                BV_NEG;
                bv(0b0100, 4)
            ],
            bv(0b1100, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_NEG;
                bv(0b0000, 4)
            ],
            bv(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_NEG;
                bv(0b1111, 4)
            ],
            bv(0b0001, 4)
        ],
    ]
}

pub fn bv_lt_tests() -> Vec<Term> {
    vec![
        term![
            BV_ULT;
            bv(0b0111, 4),
            bv(0b1111, 4)
        ],
        term![
            BV_ULT;
            bv(0b0101, 4),
            bv(0b1101, 4)
        ],
        term![
            Op::Eq;
            term![
                BV_ULT;
                bv(0b0101, 4),
                bv(0b0101, 4)
            ],
            bool(false)
        ],
        term![
            Op::Eq;
            term![
                BV_ULT;
                bv(0b0101, 4),
                bv(0b1101, 4)
            ],
            bool(false)
        ],
    ]
}

pub fn bv_and_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_AND; bv(0b1111,4), bv(0b1111,4)],
            bv(0b1111, 4)
        ],
        term![
            Op::Eq;
            term![BV_AND; bv(0b0111,4), bv(0b1101,4)],
            bv(0b0101, 4)
        ],
    ]
}
pub fn bv_or_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_OR; bv(0b1111,4), bv(0b1111,4)],
            bv(0b1111, 4)
        ],
        term![
            Op::Eq;
            term![BV_OR; bv(0b0111,4), bv(0b0101,4)],
            bv(0b0111, 4)
        ],
    ]
}
pub fn bv_add_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_ADD; bv(0b1111,4), bv(0b1111,4)],
            bv(0b1110, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv(0b1111,4), bv(0b0101,4)],
            bv(0b0100, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv(0b1111,4), bv(0b1111,4), bv(0b1111,4), bv(0b1111,4)],
            bv(0b1100, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv(0b1111,4), bv(0b1111,4), bv(0b1111,4)],
            bv(0b1101, 4)
        ],
        term![
            Op::Eq;
            term![BV_ADD; bv(0b0000,4), bv(0b1110,4), bv(0b0000,4), bv(0b0000,4)],
            bv(0b1110, 4)
        ],
    ]
}
pub fn bv_mul_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_MUL; bv(0b0001,4)],
            bv(0b0001, 4)
        ],
        term![
            Op::Eq;
            term![BV_MUL; bv(0b0000,4), bv(0b1111,4)],
            bv(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![BV_MUL; bv(0b0010,4), bv(0b1111,4)],
            bv(0b1110, 4)
        ],
        term![
            Op::Eq;
            term![BV_MUL; bv(0b1001,4), bv(0b0101,4)],
            bv(0b1101, 4)
        ],
    ]
}

pub fn bv_sext_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![
                Op::BvSext(2);
                bv(0b10, 2)
            ],
            bv(0b1110, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvSext(2);
                bv(0b01, 2)
            ],
            bv(0b0001, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvSext(2);
                term![BV_ADD; bv(0b01, 2), bv(0b01, 2)]
            ],
            bv(0b1110, 4)
        ],
    ]
}

pub fn bv_uext_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![
                Op::BvUext(2);
                bv(0b10, 2)
            ],
            bv(0b0010, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvUext(2);
                term![BV_ADD; bv(0b01, 2), bv(0b01, 2)]
            ],
            bv(0b0010, 4)
        ],
        term![
            Op::Eq;
            term![
                Op::BvUext(2);
                bv(0b01, 2)
            ],
            bv(0b0001, 4)
        ],
    ]
}
pub fn bv_sub_tests() -> Vec<Term> {
    vec![
        term![
            Op::Eq;
            term![BV_SUB; bv(0b1111,4), bv(0b1111,4)],
            bv(0b0000, 4)
        ],
        term![
            Op::Eq;
            term![BV_SUB; bv(0b1111,4), bv(0b0000,4)],
            bv(0b1111, 4)
        ],
        term![
            Op::Eq;
            term![BV_SUB; bv(0b1111,4), bv(0b1110,4)],
            bv(0b0001, 4)
        ],
        term![
            Op::Eq;
            term![BV_SUB; bv(0b0000,4), bv(0b1111,4)],
            bv(0b0001, 4)
        ],
    ]
}
