extern crate nom;
extern crate wasm;
extern crate wasm_spec;

use nom::{IResult,Err};
use std::str;

fn panic_from(test_name: &str, mut err: Err<&[u8]>) {
    loop {
        match err {
            Err::Code(kind) => panic!("Parse error in {}, (kind {:?}).", test_name, kind),
            Err::Node(_,rest) => { err = *rest }
            Err::Position(kind,pos) => panic!("Parse error in {}, (kind {:?}, pos {}...).", test_name, kind, str::from_utf8(&pos[..128]).unwrap()),
            Err::NodePosition(_,_,rest) => { err = *rest }
        }
    }
}

#[test]
fn spec_tests() {
    for (test_name, test_wast) in wasm_spec::tests() {
        match wasm::parser::text::top_level(test_wast.as_bytes()) {
            IResult::Done(_,_) => (),
            IResult::Error(err) => panic_from(test_name, err),
            IResult::Incomplete(need) => panic!("Incomplete parse in {}, {:?}.", test_name, need),
        }
    }
}
