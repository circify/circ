//! Contains a number of constant terms for testing
#![allow(missing_docs)]

use super::super::*;

#[test]
fn op_sort_eval() {
    let t = text::parse_term(b"(declare () (sort (#l (mod 11) ((#t true true) (#t true false)))))");
    let actual_output = eval(&t, &Default::default());
    let expected_output = text::parse_value_map(
        b"(let ((output (#l (mod 11) ((#t true false) (#t true true))))) false)",
    );
    assert_eq!(&actual_output, expected_output.get("output").unwrap());

    let t = text::parse_term(b"(declare () (sort (#l (mod 11) (#x0 #xf #x4 #x3))))");
    let actual_output = eval(&t, &Default::default());
    let expected_output =
        text::parse_value_map(b"(let ((output (#l (mod 11) (#x0 #x3 #x4 #xf)))) false)");
    assert_eq!(&actual_output, expected_output.get("output").unwrap());
}

#[cfg(feature = "poly")]
#[test]
fn uniq_deri_gcd_eval() {
    let t = text::parse_term(
        b"
        (declare (
         (pairs (array (mod 17) (tuple (mod 17) bool) 5))
        )
         (uniq_deri_gcd pairs))",
    );

    let inputs = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
            (pairs (#l (mod 17) ( (#t #f0 false) (#t #f1 false) (#t #f2 true) (#t #f3 false) (#t #f4 true) )))
        ) false))
        ",
    );
    let actual_output = eval(&t, &inputs);
    let expected_output = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
          (output (#t
            (#l (mod 17) ( #f16 #f0 #f0 #f0 #f0 ) ) ; s, from sage
            (#l (mod 17) ( #f7 #f9 #f0 #f0 #f0 ) ) ; t, from sage
          ))
        ) false))
        ",
    );
    assert_eq!(&actual_output, expected_output.get("output").unwrap());

    let inputs = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
            (pairs (#l (mod 17) ( (#t #f0 true) (#t #f1 true) (#t #f2 true) (#t #f3 false) (#t #f4 true) )))
        ) false))
        ",
    );
    let actual_output = eval(&t, &inputs);
    let expected_output = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
          (output (#t
            (#l (mod 17) ( #f8 #f9 #f16 #f0 #f0 ) ) ; s, from sage
            (#l (mod 17) ( #f2 #f16 #f9 #f13 #f0 ) ) ; t, from sage
          ))
        ) false))
        ",
    );
    assert_eq!(&actual_output, expected_output.get("output").unwrap());
}

#[test]
fn persistent_ram_split_eval() {
    let t = text::parse_term(
        b"
        (declare (
         (entries (array (mod 17) (tuple (mod 17) (mod 17)) 5))
         (indices (array (mod 17) (mod 17) 3))
        )
         (persistent_ram_split entries indices))",
    );

    let inputs = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
            (entries (#l (mod 17) ( (#t #f0 #f1) (#t #f1 #f1) (#t #f2 #f3) (#t #f3 #f4) (#t #f4 #f4) )))
            (indices (#l (mod 17) (#f0 #f2 #f3)))
        ) false))
        ",
    );
    let actual_output = eval(&t, &inputs);
    let expected_output = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
          (output (#t
            (#l (mod 17) ( (#t #f1 #f1) (#t #f4 #f4) )) ; untouched
            (#l (mod 17) ( (#t #f0 #f0) (#t #f2 #f2) (#t #f3 #f3) )) ; init_reads
            (#l (mod 17) ( (#t #f0 #f1) (#t #f2 #f3) (#t #f3 #f4) )) ; fin_writes
          ))
        ) false))
        ",
    );
    dbg!(&actual_output.as_tuple()[0].as_array().default);
    dbg!(
        &expected_output.get("output").unwrap().as_tuple()[0]
            .as_array()
            .default
    );
    assert_eq!(&actual_output, expected_output.get("output").unwrap());

    // duplicates
    let inputs = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
            (entries (#l (mod 17) ( (#t #f0 #f0) (#t #f1 #f2) (#t #f2 #f2) (#t #f3 #f3) (#t #f4 #f4) )))
            (indices (#l (mod 17) (#f1 #f1 #f1)))
        ) false))
        ",
    );
    let actual_output = eval(&t, &inputs);
    let expected_output = text::parse_value_map(
        b"
        (set_default_modulus 17
        (let
        (
          (output (#t
            (#l (mod 17) ( (#t #f3 #f3) (#t #f4 #f4) )) ; untouched
            (#l (mod 17) ( (#t #f0 #f0) (#t #f1 #f1) (#t #f2 #f2) )) ; init_reads
            (#l (mod 17) ( (#t #f0 #f0) (#t #f1 #f2) (#t #f2 #f2) )) ; fin_writes
          ))
        ) false))
        ",
    );
    assert_eq!(&actual_output, expected_output.get("output").unwrap());
}

fn haboeck_eval(haystack: &[usize], needles: &[usize], counts: &[usize]) {
    let t = text::parse_term(
        format!(
            "
        (declare (
         (haystack (array (mod 17) (mod 17) {}))
         (needles (array (mod 17) (mod 17) {}))
        )
         (haboeck haystack needles))",
            haystack.len(),
            needles.len()
        )
        .as_bytes(),
    );
    assert_eq!(haystack.len(), counts.len());
    let haystack: Vec<String> = haystack.iter().map(|h| format!("#f{}", h)).collect();
    let needles: Vec<String> = needles.iter().map(|h| format!("#f{}", h)).collect();
    let counts: Vec<String> = counts.iter().map(|h| format!("#f{}", h)).collect();

    let inputs = text::parse_value_map(
        format!(
            "(set_default_modulus 17
        (let
        (
            (haystack (#l (mod 17) ({})))
            (needles (#l (mod 17) ({})))
        ) false))",
            haystack.join(" "),
            needles.join(" ")
        )
        .as_bytes(),
    );
    let expected_output = text::parse_value_map(
        format!(
            "(set_default_modulus 17
        (let
        (
            (counts (#l (mod 17) ({})))
        ) false))",
            counts.join(" ")
        )
        .as_bytes(),
    );
    let actual_output = eval(&t, &inputs);
    assert_eq!(&actual_output, expected_output.get("counts").unwrap());
}

#[test]
fn haboeck_eval_2_6_full() {
    haboeck_eval(&[1, 2], &[1, 1, 2, 2, 1, 2], &[3, 3]);
}

#[test]
fn haboeck_eval_4_4_full() {
    haboeck_eval(&[1, 2, 4, 3], &[1, 2, 3, 4], &[1, 1, 1, 1]);
}

#[test]
fn haboeck_eval_6_2() {
    haboeck_eval(&[6, 8, 3, 4, 1, 2], &[1, 1], &[0, 0, 0, 0, 2, 0]);
}
