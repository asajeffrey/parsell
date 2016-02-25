// Test for typechecking blow-up
// https://github.com/rust-lang/rust/issues/31849

extern crate parsell;
use parsell::{Parser, UncommittedStr, CHARACTER};

#[test]
fn test_typecheck_time() {
    CHARACTER
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .and_then(CHARACTER)
        .init_str("hello, world");
}
