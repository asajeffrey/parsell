# parsimonious: a parser combinator library for Rust

The goal of this library is to provide parser combinators that:

* are optimized for LL(1) grammars,
* support streaming input,
* do as little buffering or copying as possible, and
* do as little dynamic method dispatch as possible.

It is based on:

* [Monadic Parsing in Haskell](http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf) by G. Hutton and E. Meijer, JFP 8(4) pp. 437-444,
* [Nom, eating data byte by byte](https://github.com/Geal/nom) by G. Couprie.

[Rustdoc](http://asajeffrey.github.io/parsimonious) |
[Crate](https://crates.io/crates/parsimonious) |
[CI](https://travis-ci.org/asajeffrey/parsimonious)

## Example

```rust
extern crate parsimonious;
use parsimonious::{character,Parser,Uncommitted,Committed,Stateful};
use parsimonious::ParseResult::{Done,Continue};
#[allow(non_snake_case)]
fn main() {

    // A sequence of alphanumerics, saved in a string buffer
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let ALPHANUMERICS = ALPHANUMERIC.star(String::new);

    // If you provide complete input to the parser, you'll get back a Done response:
    match ALPHANUMERICS.init().parse("abc123!") {
        Done("!",result) => assert_eq!(result, "abc123"),
        _ => panic!("Can't happen."),
    }

    // If you provide incomplete input to the parser, you'll get back a Continue response:
    match ALPHANUMERICS.init().parse("abc") {
        Continue("",parsing) => match parsing.parse("123!") {
            Done("!",result) => assert_eq!(result, "abc123"),
            _ => panic!("Can't happen."),
        },
        _ => panic!("Can't happen."),
    }

}
```

Example tested with [Skeptic](https://github.com/brson/rust-skeptic).
