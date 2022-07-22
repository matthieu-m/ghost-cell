#[test]
fn compile_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile_tests/ghost_cell/*.rs");
    #[cfg(feature = "experimental-ghost-cursor")]
    t.compile_fail("tests/compile_tests/ghost_cursor/*.rs");
}
