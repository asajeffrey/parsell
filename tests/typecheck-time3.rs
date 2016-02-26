// Test for typechecking blow-up
// https://github.com/rust-lang/rust/issues/31849

extern crate parsell;
use parsell::{Parser, CHARACTER, UncommittedStr};
use std::str::Chars;

#[test]
fn test_typecheck_time() {
    let parser = CHARACTER
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER)
        .or_else(CHARACTER);
    parser.init_str("Hello, world.");
}
