//! Contains a number of constant terms for testing
#![allow(missing_docs)]

use super::*;
use fxhash::FxHashMap;

#[test]
fn eq() {
    let v = var("a".to_owned(), Sort::Bool);
    let u = var("a".to_owned(), Sort::Bool);
    let w = var("b".to_owned(), Sort::Bool);
    assert_eq!(v, u);
    assert!(v != w);
    assert!(u != w);
}

#[test]
fn bv2pf() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(bvshl #b0001 #b0010)"),
            &FxHashMap::default()
        )),
        text::parse_term(b" #b0100 ")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b" (set_default_modulus 17 ((pf2bv 4) #f1)) "),
            &FxHashMap::default()
        )),
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
        let v = var("b".to_owned(), Sort::BitVector(4));
        term![
            Op::BvBit(4);
            term![
                Op::BvConcat;
                v,
                term![Op::BoolToBv; var("c".to_owned(), Sort::Bool)]
            ]
        ]
    }

    #[test]
    fn vars() {
        let v = var("a".to_owned(), Sort::Bool);
        assert_eq!(check(&v), Sort::Bool);
        let v = var("b".to_owned(), Sort::BitVector(4));
        assert_eq!(check(&v), Sort::BitVector(4));
        let v = t();
        assert_eq!(check(&v), Sort::Bool);
    }

    #[test]
    fn traversal() {
        let tt = t();
        assert_eq!(
            vec![
                Op::new_var("c".to_owned(), Sort::Bool),
                Op::BoolToBv,
                Op::new_var("b".to_owned(), Sort::BitVector(4)),
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
    bool_lit(b)
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

#[test]
fn fpsub_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsub #fp3 #fp2)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsub #fp3.333333f32 #fp0.191741f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3.141592f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsub #fp3.333333333333333 #fp0.19174067974354)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3.141592653589793")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsub #fp-3.402823466e+38f32 #fp2e31f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-Inff32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsub #fp-1.7976931348623158e+308 #fp1e292)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-Inf")
    );
}

#[test]
fn fpadd_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp1 #fp2)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp1.1111 #fp-1.1111)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp1e-324 #fp-1e-324)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp3.402823466e+38f32 #fp2e31f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInff32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp1.7976931348623158e+308 #fp1e+292)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInf")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fpInf #fp1)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInf")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp-Inf #fp1)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-Inf")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpadd #fpInff32 #fp-Inff32)"),
        &FxHashMap::default()
    ))
    .as_f32_opt()
    .unwrap()
    .is_nan());
    assert!(const_(eval(
        &text::parse_term(b"(fpadd #fpNaN #fp2)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
    assert!(const_(eval(
        &text::parse_term(b"(fpadd #fpNaN #fpNaN)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpadd #fp1.0000001f32 #fp1e-7f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0000002f32")
    );
}

#[test]
fn fpmul_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmul #fp3 #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp0")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpmul #fp-Inf #fp0)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmul #fpInf #fp2)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInf")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmul #fpInf #fp-1)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-Inf")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpmul #fpNaN #fp2)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
    assert!(const_(eval(
        &text::parse_term(b"(fpmul #fpNaN #fpNaN)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
}

#[test]
fn fpdiv_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpdiv #fp1 #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInf")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpdiv #fp-1 #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-Inf")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpdiv #fpNaN #fp2)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
}

#[test]
fn fprem_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fprem #fp3.1415 #fp3)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp0.14150000000000018")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fprem #fp3 #fp0)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
    assert!(const_(eval(
        &text::parse_term(b"(fprem #fpInf #fp2)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
}

#[test]
fn fpmax_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmax #fp2 #fp5)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp5")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmax #fpNaN #fp3)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmax #fp-0 #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-0") // interesting
    );
}

#[test]
fn fpmin_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpmin #fp-3 #fp2)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-3")
    );
}

#[test]
fn fpneg_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpneg #fp3)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-3")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpneg #fp-4.5)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp4.5")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpneg #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpneg #fpInf)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-Inf")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpneg #fp-Inf)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInf")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpneg #fpNan)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
}

#[test]
fn fpabs_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpabs #fp-7)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp7")
    );
}

#[test]
fn fpsqrt_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsqrt #fp12.25)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3.5")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpsqrt #fp-4)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
}

#[test]
fn fpround_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpround #fp2.5)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpround #fp2.3)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp2")
    );
    assert!(const_(eval(
        &text::parse_term(b"(fpround #fpNan)"),
        &FxHashMap::default()
    ))
    .as_f64_opt()
    .unwrap()
    .is_nan());
}

#[test]
fn fpge_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpge #fp5 #fp3)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpge #fp3 #fp5)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpge #fp4 #fp4)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpge #fpNaN #fp2)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
}

#[test]
fn fpgt_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpgt #fp4 #fp4)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpgt #fpInf #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
}

#[test]
fn fple_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fple #fpNaN #fp2)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
}

#[test]
fn fplt_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fplt #fp-Inf #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
}

#[test]
fn fpeq_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpeq #fp1.0 #fp1)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpeq (fpadd #fp0.1 #fp0.2) #fp0.3)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpeq #fpNaN #fpNaN)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
}

#[test]
fn fpnormal_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnormal #fp0.01)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );

    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnormal #fp1.17549435e-39f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
}

#[test]
fn fpsubnormal_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsubnormal #fp0.01)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );

    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpsubnormal #fp1.17549435e-39f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
}

#[test]
fn fpzero_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpzero #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpzero #fp-0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpzero #fp1e-45f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
}

#[test]
fn fpinfinite_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpinfinite #fpInf)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpinfinite #fp-Inf)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpinfinite #fp1.7976931348623158e+308)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpinfinite #fp1.7976931348623159e+308)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
}

#[test]
fn fpnan_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnan #fpNaN)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnan #fpInf)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnan #fp3.14)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"false")
    );
}

#[test]
fn fpnegative_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnegative #fp-2.5)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fpnegative #fp-0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
}

#[test]
fn fppositive_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fppositive #fp3.7)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(fppositive #fp0)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"true")
    );
}

#[test]
fn bv2fp_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(bv2fp #b00111111100000000000000000000000)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(bv2fp #b00000000000000000000000000000000)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp0f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(
                b"(bv2fp #b0011111111110000000000000000000000000000000000000000000000000000)"
            ),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(
                b"(bv2fp #b0000000000000000000000000000000000000000000000000000000000000000)"
            ),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(
                b"(bv2fp #b1000000000000000000000000000000000000000000000000000000000000000)"
            ),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-0")
    );
}

#[test]
fn ubv2fp_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((ubv2fp 32) #x0001)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((ubv2fp 64) #x0001)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((ubv2fp 64) #xffffffff)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp4294967295.0")
    );
}

#[test]
fn sbv2fp_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((sbv2fp 64) #xffffffffffffffff)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp-1.0")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((sbv2fp 64) #x7fffffff)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp2147483647.0")
    );
}

#[test]
fn fp2fp_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((fp2fp 64) #fp1.0f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0f64")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((fp2fp 32) #fp16777217.0f64)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp16777216.0f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"((fp2fp 32) #fp2.5f32)"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp2.5f32")
    );
}

#[test]
fn pf2fp_tests() {
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(set_default_modulus 17 ((pf2fp 32) #f1))"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp1.0f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(set_default_modulus 17 ((pf2fp 32) #f20))"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp3.0f32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(b"(set_default_modulus 17 ((pf2fp 32) #f17))"),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp17f32") // shouldn't this be 0?
    );
    let p: Integer = Integer::from(1) << (512 - 1); // Mersenne prime
    let overflow_f32: Integer = p.clone() - 1;
    assert_eq!(
        const_(eval(
            &text::parse_term(
                format!("(set_default_modulus {p} ((pf2fp 32) #f{overflow_f32}))").as_bytes()
            ),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fpInff32")
    );
    assert_eq!(
        const_(eval(
            &text::parse_term(
                format!("(set_default_modulus {p} ((pf2fp 64) #f{overflow_f32}))").as_bytes()
            ),
            &FxHashMap::default()
        )),
        text::parse_term(b"#fp6.703903964971298e+153")
    );
}
