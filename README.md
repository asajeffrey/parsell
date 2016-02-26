# Parsell: an LL(1) streaming parser combinator library for Rust

The goal of this library is to provide parser combinators that:

* are optimized for LL(1) grammars,
* support streaming input,
* do as little buffering or copying as possible, and
* do as little dynamic method dispatch as possible.

It is based on:

* [Monadic Parsing in Haskell](http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf) by G. Hutton and E. Meijer, JFP 8(4) pp. 437-444,
* [Nom, eating data byte by byte](https://github.com/Geal/nom) by G. Couprie.

[Rustdoc](http://asajeffrey.github.io/parsell) |
[Video](https://air.mozilla.org/bay-area-rust-meetup-february-2016/) |
[Slides](http://asajeffrey.github.io/parsell/doc/talks/sf-rust-2016-02-18/) |
[Crate](https://crates.io/crates/parsell) |
[CI](https://travis-ci.org/asajeffrey/parsell)

## Example

```
extern crate parsell;
use parsell::{character,Parser,UncommittedStr,StatefulStr};
use parsell::ParseResult::{Done,Continue};
#[allow(non_snake_case)]
fn main() {

    // A sequence of alphanumerics, saved in a string buffer
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let ALPHANUMERICS = ALPHANUMERIC.plus(String::new);

    // If you provide unmatching input to the parser, you'll get back a None response:
    match ALPHANUMERICS.init_str("!$?") {
        None => (),
        _ => panic!("Can't happen."),
    }

    // If you provide complete input to the parser, you'll get back a Done response:
    match ALPHANUMERICS.init_str("abc123!") {
        Some(Done(result)) => assert_eq!(result, "abc123"),
        _ => panic!("Can't happen."),
    }

    // If you provide incomplete input to the parser, you'll get back a Continue response:
    match ALPHANUMERICS.init_str("abc") {
        Some(Continue(parsing)) => match parsing.more_str("123!") {
            Done(result) => assert_eq!(result, "abc123"),
            _ => panic!("Can't happen."),
        },
        _ => panic!("Can't happen."),
    }

}
```

Example tested with [Skeptic](https://github.com/brson/rust-skeptic).
