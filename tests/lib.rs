// extern crate nom;
// extern crate wasm;
// extern crate wasm_spec;

// use nom::{IResult,Err};
// use std::str;

// fn print(mut err: Err<&[u8]>) {
//     loop {
//         match err {
//             Err::Code(kind) => { println!("Kind {:?}.", kind); return; }
//             Err::Node(kind, rest) => { println!("Nested kind {:?}" , kind); err = *rest }
//             Err::Position(kind,pos) => { println!("Kind {:?} at {}...", kind, str::from_utf8(&pos[..32]).unwrap()); return; }
//             Err::NodePosition(kind, pos, rest) => { println!("Nested kind {:?} at {}...", kind, str::from_utf8(&pos[..32]).unwrap()); err = *rest }
//         }
//     }
// }

// #[test]
// fn spec_tests() {
//     for (test_name, test_wast) in wasm_spec::tests() {
//         match wasm::parser::text::top_level(test_wast.as_bytes()) {
//             IResult::Done(_,_) => (),
//             IResult::Error(err) => { print(err); panic!("Parse error in {}", test_name) },
//             IResult::Incomplete(need) => panic!("Incomplete parse in {}, {:?}.", test_name, need),
//         }
//     }
// }
