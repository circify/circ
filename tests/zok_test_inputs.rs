//! The input contract of `ZSharpCurlyFE::eval_test_inputs`: which `@test`
//! annotations are accepted, how their input expressions are typed and
//! evaluated, and which malformed annotations are rejected (and how).
//!
//! Each test writes its program to a uniquely named file in the OS temp dir,
//! so nothing touches the source tree and tests can run in parallel.

#![cfg(all(feature = "smt", feature = "zokc"))]

use circ::front::zsharpcurly::{TestBackend, TestCase, ZSharpCurlyFE};
use circ::front::Mode;
use circ::ir::term::Value;
use std::sync::Once;

static INIT: Once = Once::new();

/// A temp file that is deleted on drop — even when the test panics, so
/// failing tests don't leave files behind.
struct TempZok(std::path::PathBuf);

impl Drop for TempZok {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Write `src` to a unique temp file and run eval_test_inputs on it.
fn eval(test_name: &str, src: &str) -> Result<Vec<TestCase>, String> {
    // The CirC config is process-global and can only be set once.
    INIT.call_once(circ::cfg::set_default);
    // The process id keeps concurrent `cargo test` processes from colliding
    // on the same paths; the test name separates threads within a process.
    let path = std::env::temp_dir().join(format!(
        "zok_test_inputs_{}_{}.zok",
        std::process::id(),
        test_name
    ));
    std::fs::write(&path, src).unwrap();
    let guard = TempZok(path);
    ZSharpCurlyFE::eval_test_inputs(guard.0.clone(), Mode::Proof)
}

/// Assert a Value is a field element with the given integer value.
fn assert_field(v: &Value, expected: u64) {
    match v {
        Value::Field(f) => assert_eq!(f.i(), expected),
        other => panic!("expected field {}, got {:?}", expected, other),
    }
}

/// Assert a Value is a bit-vector of the given width and integer value.
fn assert_uint(v: &Value, width: usize, expected: u64) {
    match v {
        Value::BitVector(b) => {
            assert_eq!(b.width(), width);
            assert_eq!(*b.uint(), expected);
        }
        other => panic!("expected u{} {}, got {:?}", width, expected, other),
    }
}

/// Unwrap a Value::Array into its element Values, in index order.
fn array_values(v: &Value) -> Vec<Value> {
    match v {
        Value::Array(a) => a.values(),
        other => panic!("expected array, got {:?}", other),
    }
}

fn tuple_values(v: &Value) -> &[Value] {
    match v {
        Value::Tuple(values) => values,
        other => panic!("expected tuple, got {:?}", other),
    }
}

/// Assert a Value is an array of field elements with the given values.
fn assert_field_array(v: &Value, expected: &[u64]) {
    let vals = array_values(v);
    assert_eq!(vals.len(), expected.len(), "array length");
    for (v, e) in vals.iter().zip(expected) {
        assert_field(v, *e);
    }
}

/// A temp directory that is deleted on drop, with everything in it.
struct TempDir(std::path::PathBuf);

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Write several files into a unique temp directory — so sibling imports
/// resolve by bare name, like the examples import "xor" — and run
/// eval_test_inputs on the first one.
fn eval_files(test_name: &str, files: &[(&str, &str)]) -> Result<Vec<TestCase>, String> {
    INIT.call_once(circ::cfg::set_default);
    let dir = std::env::temp_dir().join(format!(
        "zok_test_inputs_{}_{}",
        std::process::id(),
        test_name
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let guard = TempDir(dir);
    for (name, src) in files {
        std::fs::write(guard.0.join(name), src).unwrap();
    }
    ZSharpCurlyFE::eval_test_inputs(guard.0.join(files[0].0), Mode::Proof)
}

#[test]
fn constant_arithmetic_evaluates() {
    let tests = eval(
        "constant_arithmetic",
        r#"@test y = 3 * 3;
def test_sq(private field y) {
    assert(y == 9);
}
"#,
    )
    .unwrap();
    assert_eq!(tests.len(), 1);
    assert_eq!(tests[0].name(), "test_sq");
    assert_eq!(tests[0].inputs().len(), 1);
    assert_eq!(tests[0].inputs()[0].name(), "y");
    assert_eq!(tests[0].inputs()[0].source(), "3 * 3");
    assert_field(tests[0].inputs()[0].value(), 9);
}

#[test]
fn named_constant_resolves() {
    let tests = eval(
        "named_constant",
        r#"const field C = 7;

@test x = C + 1;
def test_c(private field x) {
    assert(x == 8);
}
"#,
    )
    .unwrap();
    assert_field(tests[0].inputs()[0].value(), 8);
}

#[test]
fn const_function_call_evaluates() {
    // The const evaluator supports calls to (non-generic, constant-input)
    // functions; "non-constant" means evaluator-rejected, not "contains a
    // call".
    let tests = eval(
        "const_fn_call",
        r#"def sq(field a) -> field {
    return a * a;
}

@test y = sq(3);
def test_sq(private field y) {
    assert(y == 9);
}
"#,
    )
    .unwrap();
    assert_field(tests[0].inputs()[0].value(), 9);
}

#[test]
fn all_scalar_types_evaluate() {
    let tests = eval(
        "all_scalars",
        r#"@test b = true, n8 = 4u8, n16 = 4u16, n32 = 4u32, n64 = 4u64, f = 5f;
def test_scalars(private bool b, private u8 n8, private u16 n16, private u32 n32, private u64 n64, private field f) {
    assert(b);
}
"#,
    )
    .unwrap();
    let inputs = tests[0].inputs();
    assert_eq!(inputs.len(), 6);
    assert!(matches!(inputs[0].value(), Value::Bool(true)));
    assert_uint(inputs[1].value(), 8, 4);
    assert_uint(inputs[2].value(), 16, 4);
    assert_uint(inputs[3].value(), 32, 4);
    assert_uint(inputs[4].value(), 64, 4);
    assert_field(inputs[5].value(), 5);
}

#[test]
fn unsuffixed_literal_typed_by_parameter() {
    // The key typing rule: a bare `2` binding to a u32 parameter must come
    // back as a 32-bit bit-vector, not as a field element.
    let tests = eval(
        "unsuffixed_u32",
        r#"@test x = 2;
def test_u(private u32 x) {
    assert(x == 2u32);
}
"#,
    )
    .unwrap();
    assert_uint(tests[0].inputs()[0].value(), 32, 2);
}

#[test]
fn bare_test_zero_params_ok() {
    let tests = eval(
        "bare_zero_params",
        r#"@test;
def test_noargs() {
    assert(true);
}
"#,
    )
    .unwrap();
    assert_eq!(tests[0].name(), "test_noargs");
    assert!(tests[0].inputs().is_empty());
}

#[test]
fn bare_test_with_params_rejected() {
    let err = eval(
        "bare_with_params",
        r#"@test;
def test_missing(private field x) {
    assert(x == x);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("missing a value for parameter x"), "{}", err);
}

#[test]
fn missing_input_rejected() {
    let err = eval(
        "missing_input",
        r#"@test a = 1;
def test_two(private field a, private field b) {
    assert(a == a);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("missing a value for parameter b"), "{}", err);
}

#[test]
fn unknown_input_rejected() {
    let err = eval(
        "unknown_input",
        r#"@test a = 1, nope = 2;
def test_one(private field a) {
    assert(a == a);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("nope does not match any parameter"), "{}", err);
}

#[test]
fn duplicate_input_rejected() {
    let err = eval(
        "duplicate_input",
        r#"@test a = 1, a = 2;
def test_dup(private field a) {
    assert(a == a);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("duplicate @test input a"), "{}", err);
}

#[test]
fn non_constant_expression_rejected() {
    let err = eval(
        "non_constant",
        r#"@test x = undefined_thing;
def test_bad(private field x) {
    assert(x == x);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("undefined_thing"), "{}", err);
}

#[test]
fn array_parameter_accepted() {
    let tests = eval(
        "array_param",
        r#"@test xs = [1, 2];
def test_arr(private field[2] xs) {
    assert(xs[0] + xs[1] == 3);
}
"#,
    )
    .unwrap();
    assert_eq!(tests[0].inputs()[0].source(), "[1, 2]");
    assert_field_array(tests[0].inputs()[0].value(), &[1, 2]);
}

#[test]
fn nested_array_accepted() {
    let tests = eval(
        "nested_array",
        r#"@test A = [[1, 2], [3, 4]];
def test_mat(private field[2][2] A) {
    assert(A[0][0] == 1);
}
"#,
    )
    .unwrap();
    let rows = array_values(tests[0].inputs()[0].value());
    assert_field_array(&rows[0], &[1, 2]);
    assert_field_array(&rows[1], &[3, 4]);
}

#[test]
fn array_input_flattens_to_leaf_names() {
    // The naming contract the proof pipeline relies on: one entry per leaf,
    // dotted indices, outermost dimension first, in index order — the same
    // names declare_input gives the circuit's input variables (on-disk
    // ground truth: examples/ZoKratesCurly/pf/mm.zok.pin).
    let tests = eval(
        "flatten_names",
        r#"@test A = [[1, 2], [3, 4]], y = 5;
def test_flat(private field[2][2] A, public field y) {
    assert(A[0][0] + y == 6);
}
"#,
    )
    .unwrap();
    let entries = tests[0].inputs()[0].flat_entries();
    let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["A.0.0", "A.0.1", "A.1.0", "A.1.1"]);
    for ((_, v), e) in entries.iter().zip([1u64, 2, 3, 4]) {
        assert_field(v, e);
    }
    // A scalar flattens to a single entry under the bare parameter name.
    assert_eq!(
        tests[0].inputs()[1].flat_entries(),
        vec![("y".to_string(), tests[0].inputs()[1].value().clone())]
    );
}

#[test]
fn non_square_array_flattens_row_major() {
    // A non-square field[2][3] pins the dimension order: a transposition bug
    // (column-major) would relabel M.0.2 as M.2.0 (out of range) — a square
    // matrix can't expose that. Leaves are row-major: M.0.0 .. M.1.2.
    let tests = eval(
        "flatten_non_square",
        r#"@test M = [[1, 2, 3], [4, 5, 6]];
def test_ns(private field[2][3] M) {
    assert(M[0][0] == 1);
}
"#,
    )
    .unwrap();
    let entries = tests[0].inputs()[0].flat_entries();
    let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["M.0.0", "M.0.1", "M.0.2", "M.1.0", "M.1.1", "M.1.2"]
    );
    for ((_, v), e) in entries.iter().zip([1u64, 2, 3, 4, 5, 6]) {
        assert_field(v, e);
    }
}

#[test]
fn three_dimensional_array_flattens() {
    // Three dimensions: one dotted index per level, outermost first.
    let tests = eval(
        "flatten_3d",
        r#"@test T = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]];
def test_3d(private field[2][2][2] T) {
    assert(T[0][0][0] == 1);
}
"#,
    )
    .unwrap();
    let entries = tests[0].inputs()[0].flat_entries();
    let names: Vec<&str> = entries.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["T.0.0.0", "T.0.0.1", "T.0.1.0", "T.0.1.1", "T.1.0.0", "T.1.0.1", "T.1.1.0", "T.1.1.1"]
    );
    for ((_, v), e) in entries.iter().zip([1u64, 2, 3, 4, 5, 6, 7, 8]) {
        assert_field(v, e);
    }
}

#[test]
fn array_initializer_accepted() {
    // [0; 4] const-folds to a sparse Value::Array (empty backing map, every
    // leaf comes from the default); flattening must still yield all leaves.
    let tests = eval(
        "array_fill",
        r#"@test xs = [0; 4];
def test_fill(private field[4] xs) {
    assert(xs[3] == 0);
}
"#,
    )
    .unwrap();
    assert_field_array(tests[0].inputs()[0].value(), &[0, 0, 0, 0]);
    assert_eq!(tests[0].inputs()[0].flat_entries().len(), 4);
}

#[test]
fn spread_in_array_accepted() {
    let tests = eval(
        "array_spread",
        r#"@test xs = [...[1, 2], 3];
def test_spread(private field[3] xs) {
    assert(xs[2] == 3);
}
"#,
    )
    .unwrap();
    assert_field_array(tests[0].inputs()[0].value(), &[1, 2, 3]);
}

#[test]
fn named_const_array_resolves() {
    // "Large inputs pointed at by name", same-file half: the annotation
    // names a constant instead of spelling the array out.
    let tests = eval(
        "const_array",
        r#"const field[2][2] IMG = [[1, 0], [0, 1]];

@test A = IMG;
def test_img(private field[2][2] A) {
    assert(A[0][0] == 1);
}
"#,
    )
    .unwrap();
    let rows = array_values(tests[0].inputs()[0].value());
    assert_field_array(&rows[0], &[1, 0]);
    assert_field_array(&rows[1], &[0, 1]);
}

#[test]
fn imported_const_array_resolves() {
    // "Large inputs pointed at by name", imported half: the const lives in
    // a sibling file, imported by bare name.
    let tests = eval_files(
        "imported_const_array",
        &[
            (
                "main.zok",
                r#"from "helper" import IMG;

@test A = IMG;
def test_img(private field[2][2] A) {
    assert(A[0][0] == 1);
}
"#,
            ),
            ("helper.zok", "const field[2][2] IMG = [[1, 0], [0, 1]];\n"),
        ],
    )
    .unwrap();
    let rows = array_values(tests[0].inputs()[0].value());
    assert_field_array(&rows[0], &[1, 0]);
    assert_field_array(&rows[1], &[0, 1]);
}

#[test]
fn array_elements_typed_by_parameter() {
    // Literal typing descends into inline arrays: bare 1/2/3 binding to a
    // u32[3] parameter come back as 32-bit bit-vectors.
    let tests = eval(
        "uint_array",
        r#"@test xs = [1, 2, 3];
def test_u32s(private u32[3] xs) {
    assert(xs[0] == 1u32);
}
"#,
    )
    .unwrap();
    let vals = array_values(tests[0].inputs()[0].value());
    for (i, v) in vals.iter().enumerate() {
        assert_uint(v, 32, (i + 1) as u64);
    }
}

#[test]
fn bool_array_accepted() {
    let tests = eval(
        "bool_array",
        r#"@test bs = [true, false];
def test_bools(private bool[2] bs) {
    assert(bs[0]);
}
"#,
    )
    .unwrap();
    let vals = array_values(tests[0].inputs()[0].value());
    assert!(matches!(vals[0], Value::Bool(true)));
    assert!(matches!(vals[1], Value::Bool(false)));
}

#[test]
fn array_wrong_length_rejected() {
    // The type-equality check works structurally on arrays: a 2-element
    // value cannot bind to a field[3] parameter, and the diagnostic names
    // both types.
    let err = eval(
        "array_len",
        r#"@test xs = [1, 2];
def test_len(private field[3] xs) {
    assert(xs[0] == 1);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("expected type field[3]"), "{}", err);
    assert!(err.contains("field[2]"), "{}", err);
}

#[test]
fn array_wrong_element_type_rejected() {
    let err = eval(
        "array_elem_ty",
        r#"@test xs = [true, false];
def test_elem_ty(private field[2] xs) {
    assert(xs[0] == 1);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("expected type field[2]"), "{}", err);
    assert!(err.contains("bool"), "{}", err);
}

#[test]
fn struct_parameter_rejected() {
    let err = eval(
        "struct_param",
        r#"struct Point {
    field x;
    field y;
}

@test p = Point { x: 1, y: 2 };
def test_pt(private Point p) {
    assert(p.x == 1);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("unsupported type"), "{}", err);
    assert!(err.contains("arrays, and tuples"), "{}", err);
}

#[test]
fn mixed_scalar_tuple_accepted() {
    let tests = eval(
        "tuple_param",
        r#"@test t = (1, 2, true);
def test_tup(private (field, u32, bool) t) {
    assert(t.0 == 1);
    assert(t.1 == 2u32);
    assert(t.2);
}
"#,
    )
    .unwrap();

    let input = &tests[0].inputs()[0];
    let values = tuple_values(input.value());
    assert_field(&values[0], 1);
    assert_uint(&values[1], 32, 2);
    assert!(matches!(values[2], Value::Bool(true)));

    let entries = input.flat_entries();
    let names: Vec<&str> = entries.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["t.0", "t.1", "t.2"]);
}

#[test]
fn nested_tuple_and_array_accepted() {
    let tests = eval(
        "nested_tuple",
        r#"@test t = ([1, 2], (true, 3));
def test_nested(private (field[2], (bool, u32)) t) {
    assert(t.0[1] == 2);
    assert(t.1.0);
    assert(t.1.1 == 3u32);
}
"#,
    )
    .unwrap();

    let entries = tests[0].inputs()[0].flat_entries();
    let names: Vec<&str> = entries.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["t.0.0", "t.0.1", "t.1.0", "t.1.1"]);
}

#[test]
fn array_of_tuples_accepted() {
    let tests = eval(
        "array_of_tuples",
        r#"@test pairs = [(1, 2), (3, 4)];
def test_pairs(private (field, u32)[2] pairs) {
    assert(pairs[0].0 == 1);
    assert(pairs[1].1 == 4u32);
}
"#,
    )
    .unwrap();

    let entries = tests[0].inputs()[0].flat_entries();
    let names: Vec<&str> = entries.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["pairs.0.0", "pairs.0.1", "pairs.1.0", "pairs.1.1"]);
}

#[test]
fn empty_tuple_rejected() {
    let err = eval(
        "empty_tuple",
        r#"@test t = ();
def test_empty(private () t) {
    assert(true);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("empty array or tuple"), "{}", err);
}

#[test]
fn wrong_tuple_length_rejected() {
    let err = eval(
        "tuple_length",
        r#"@test t = (1,);
def test_length(private (field, u32) t) {
    assert(t.0 == 1);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("tuple has 1 element, expected 2"), "{}", err);
}

#[test]
fn wrong_tuple_element_type_rejected() {
    let err = eval(
        "tuple_element_type",
        r#"@test t = (true, 2);
def test_type(private (field, u32) t) {
    assert(t.0 == 1);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("expected type (field, u32)"), "{}", err);
    assert!(err.contains("(bool, u32)"), "{}", err);
}

#[test]
fn singleton_tuple_accepted() {
    let tests = eval(
        "singleton_tuple",
        r#"@test t = (5,);
def test_single(private (field,) t) {
    assert(t.0 == 5);
}
"#,
    )
    .unwrap();

    let input = &tests[0].inputs()[0];
    let values = tuple_values(input.value());
    assert_eq!(values.len(), 1);
    assert_field(&values[0], 5);

    let entries = input.flat_entries();
    let names: Vec<&str> = entries.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["t.0"]);
}

#[test]
fn named_tuple_constant_accepted() {
    let tests = eval(
        "named_tuple_const",
        r#"const (field, u32) T = (7, 9);

@test t = T;
def test_const(private (field, u32) t) {
    assert(t.0 == 7);
    assert(t.1 == 9u32);
}
"#,
    )
    .unwrap();

    let input = &tests[0].inputs()[0];
    let values = tuple_values(input.value());
    assert_field(&values[0], 7);
    assert_uint(&values[1], 32, 9);

    let entries = input.flat_entries();
    let names: Vec<&str> = entries.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names, ["t.0", "t.1"]);
}

#[test]
fn postfix_on_tuple_literal_rejected() {
    // Must be a contextual Err, not a panic.
    let err = eval(
        "postfix_tuple_literal",
        r#"@test x = (1, 2).0;
def test_access(private field x) {
    assert(x == 1);
}
"#,
    )
    .unwrap_err();
    assert!(
        err.contains("postfix expression base must be a named identifier"),
        "{}",
        err
    );
}

#[test]
fn tuple_literal_for_scalar_rejected() {
    let err = eval(
        "tuple_for_scalar",
        r#"@test x = (1, 2);
def test_scalar(private field x) {
    assert(x == 1);
}
"#,
    )
    .unwrap_err();
    assert!(
        err.contains("tuple expression used where field is expected"),
        "{}",
        err
    );
}

#[test]
fn paren_literal_for_singleton_tuple_rejected() {
    // `(4)` is a parenthesized expression, not a 1-tuple, so the literal
    // cannot satisfy the tuple hint.
    let err = eval(
        "paren_singleton",
        r#"@test t = (4);
def test_paren(private (field,) t) {
    assert(t.0 == 4);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("incompatible type"), "{}", err);
}

#[test]
fn array_of_struct_rejected() {
    let err = eval(
        "arr_of_struct",
        r#"struct Point {
    field x;
    field y;
}

@test ps = [Point { x: 1, y: 2 }, Point { x: 3, y: 4 }];
def test_pts(private Point[2] ps) {
    assert(ps[0].x == 1);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("unsupported type"), "{}", err);
}

#[test]
fn array_type_alias_accepted() {
    // The resolved-Ty rule extends to arrays: an alias for field[2][2]
    // resolves to an array of scalars and must be accepted.
    let tests = eval(
        "array_alias",
        r#"type Mat = field[2][2];

@test A = [[1, 2], [3, 4]];
def test_alias(private Mat A) {
    assert(A[0][0] == 1);
}
"#,
    )
    .unwrap();
    let rows = array_values(tests[0].inputs()[0].value());
    assert_field_array(&rows[0], &[1, 2]);
}

#[test]
fn zero_length_array_rejected() {
    // A zero-length input would flatten to no circuit inputs at all — a
    // silent no-op — so the door rejects the type outright.
    let err = eval(
        "zero_len_param",
        r#"@test xs = [0; 0];
def test_zero(private field[0] xs) {
    assert(true);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("empty array or tuple"), "{}", err);
}

#[test]
fn empty_array_value_rejected() {
    // `[]` fails const evaluation ("Empty array") before the type check.
    let err = eval(
        "empty_array_value",
        r#"@test xs = [];
def test_empty(private field[2] xs) {
    assert(xs[0] == 0);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("Empty array"), "{}", err);
}

#[test]
fn scalar_type_alias_accepted() {
    // A `type` alias for a scalar resolves to a scalar Ty and must be
    // accepted, even though it parses as a named (non-Basic) type.
    let tests = eval(
        "scalar_alias",
        r#"type Word = u32;

@test x = 2;
def test_alias(private Word x) {
    assert(x == 2u32);
}
"#,
    )
    .unwrap();
    assert_uint(tests[0].inputs()[0].value(), 32, 2);
}

#[test]
fn generic_test_function_rejected() {
    let err = eval(
        "generic_fn",
        r#"@test x = 1;
def test_gen<N>(private field x) {
    assert(x == x);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("cannot be generic"), "{}", err);
}

#[test]
fn type_mismatch_rejected() {
    // `true` cannot bind to a field parameter; the diagnostic must name
    // both the expected and the actual type.
    let err = eval(
        "type_mismatch",
        r#"@test x = true;
def test_ty(private field x) {
    assert(x == x);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("expected type field"), "{}", err);
    assert!(err.contains("bool"), "{}", err);
}

#[test]
fn annotation_sees_later_declarations() {
    // Annotation expressions have module-wide visibility: they are
    // evaluated after every declaration is processed, so forward references
    // to constants and functions declared later in the file work.
    let tests = eval(
        "decl_order",
        r#"@test x = LATER + double(2);
def test_order(private field x) {
    assert(x == 14);
}

const field LATER = 10;

def double(field n) -> field {
    return n + n;
}
"#,
    )
    .unwrap();
    assert_field(tests[0].inputs()[0].value(), 14);
}

#[test]
fn call_arguments_not_typed_by_parameter() {
    // Known limit: parameter-directed literal typing does not descend into
    // call arguments, so the bare `2` defaults to field and clashes with
    // id's u32 parameter...
    let err = eval(
        "call_arg_bare",
        r#"def id(u32 x) -> u32 {
    return x;
}

@test y = id(2);
def test_id(private u32 y) {
    assert(y == 2u32);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("mismatch"), "{}", err);

    // ...suffixing the literal is the supported form.
    let tests = eval(
        "call_arg_suffixed",
        r#"def id(u32 x) -> u32 {
    return x;
}

@test y = id(2u32);
def test_id(private u32 y) {
    assert(y == 2u32);
}
"#,
    )
    .unwrap();
    assert_uint(tests[0].inputs()[0].value(), 32, 2);
}

#[test]
fn inputs_returned_in_parameter_order() {
    // Annotation lists b before a; results follow the signature: a, then b.
    let tests = eval(
        "param_order",
        r#"@test b = 2, a = 1;
def test_order(private field a, private field b) {
    assert(a == 1);
}
"#,
    )
    .unwrap();
    assert_eq!(tests[0].inputs()[0].name(), "a");
    assert_field(tests[0].inputs()[0].value(), 1);
    assert_eq!(tests[0].inputs()[1].name(), "b");
    assert_field(tests[0].inputs()[1].value(), 2);
}

#[test]
fn visibility_captured_per_parameter() {
    // private -> public: false; public -> true; no keyword defaults to
    // public, matching the frontend's interpret_visibility.
    let tests = eval(
        "visibility",
        r#"@test a = 1, b = 2, c = 3;
def test_vis(private field a, public field b, field c) {
    assert(a + b + c == 6);
}
"#,
    )
    .unwrap();
    let inputs = tests[0].inputs();
    assert!(!inputs[0].public(), "private a");
    assert!(inputs[1].public(), "public b");
    assert!(inputs[2].public(), "unannotated c defaults to public");
}

#[test]
fn return_typed_test_rejected() {
    let err = eval(
        "return_typed",
        r#"@test y = 2;
def test_return_style(private field y) -> field {
    return y;
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("cannot declare a return type"), "{}", err);
}

#[test]
fn backend_settings_are_discovered() {
    let tests = eval(
        "backend_settings",
        r#"@test;
def test_default() {
    assert(true);
}

@test();
def test_empty_settings() {
    assert(true);
}

@test(backend = groth16);
def test_groth16() {
    assert(true);
}

@test(backend = mirage) x = 4;
def test_mirage(private field x) {
    assert(x == 4);
}
"#,
    )
    .unwrap();

    assert_eq!(tests.len(), 4);
    assert_eq!(tests[0].settings().backend(), TestBackend::Groth16);
    assert_eq!(tests[1].settings().backend(), TestBackend::Groth16);
    assert_eq!(tests[2].settings().backend(), TestBackend::Groth16);
    assert_eq!(tests[3].settings().backend(), TestBackend::Mirage);
    assert_eq!(tests[3].inputs()[0].name(), "x");
    assert_field(tests[3].inputs()[0].value(), 4);
}

#[test]
fn backend_can_still_be_an_input_name() {
    let tests = eval(
        "backend_input",
        r#"@test backend = 3;
def test_backend_input(private field backend) {
    assert(backend == 3);
}
"#,
    )
    .unwrap();

    assert_eq!(tests[0].settings().backend(), TestBackend::Groth16);
    assert_eq!(tests[0].inputs()[0].name(), "backend");
}

#[test]
fn duplicate_backend_setting_rejected() {
    let err = eval(
        "duplicate_backend",
        r#"@test(backend = groth16, backend = mirage);
def test_duplicate() {
    assert(true);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("duplicate @test setting backend"), "{}", err);
}

#[test]
fn unknown_test_setting_rejected() {
    let err = eval(
        "unknown_setting",
        r#"@test(backnd = groth16);
def test_unknown() {
    assert(true);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("unknown @test setting backnd"), "{}", err);
}

#[test]
fn unsupported_backend_rejected() {
    let err = eval(
        "unsupported_backend",
        r#"@test(backend = spartan);
def test_spartan() {
    assert(true);
}
"#,
    )
    .unwrap_err();
    assert!(err.contains("unsupported @test backend spartan"), "{}", err);
    assert!(err.contains("groth16, mirage"), "{}", err);
}

#[test]
fn plain_functions_skipped() {
    let tests = eval(
        "plain_skipped",
        r#"def helper(field n) -> field {
    return n + 1;
}

@test x = 1;
def test_only(private field x) {
    assert(x == 1);
}
"#,
    )
    .unwrap();
    assert_eq!(tests.len(), 1);
    assert_eq!(tests[0].name(), "test_only");
}

#[test]
fn malformed_file_panics() {
    // Documents current behavior: parse errors are panics inside the
    // frontend (via ZLoad), not Errs. Runners must catch_unwind (as
    // examples/ztest.rs does) until a fallible loader API exists.
    let result = std::panic::catch_unwind(|| eval("malformed", "def broken( {"));
    assert!(result.is_err());
}
