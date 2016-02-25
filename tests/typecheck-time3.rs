// Test for typechecking blow-up
// https://github.com/rust-lang/rust/issues/31849

extern crate parsell;
use parsell::{Parser, CHARACTER};
use parsell::{HasState, HasOutput, Stateless, Stateful};

use std::str::Chars;

fn must_be_parser<P>(_: P)
    where P: HasState + for<'a> Stateless<<P as HasState>::State, Chars<'a>, Option<char>>
{
}

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
    must_be_parser(parser);
}
