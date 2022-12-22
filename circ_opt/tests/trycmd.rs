#[test]
fn trycmd() {
    trycmd::TestCases::new()
        .register_bins(trycmd::cargo::compile_examples([]).unwrap())
        .case("README.md");
}
