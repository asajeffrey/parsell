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

To parse a sequence of alphanumerics into a string buffer:
```rust
    let ALPHANUMERIC = character_guard(char::is_alphanumeric);
    let ALPHANUMERICS = ALPHANUMERIC.star(String::new);
```
If you provide complete input to the parser, you will get back a `Done` response, for example:
```rust
    if let Done(rest,result) = ALPHANUMERICS.init().parse("abc123!") {
        println!("Matched {} with left over {}.", result, rest);
    }
```
prints:
```
    Matched abc123 with left over !.
```
If you provide incomplete input, you will get back a `Continue` response, for example:
```rust
    if let Continue(parsing) = ALPHANUMERICS.init().parse("abc") {
        println!("Still going...");
        if let Done(rest,result) = parsing.parse("123!") {
            println!("Matched {} with left over {}.", result, rest);
        }
    }
```
prints:
```
    Still going...
    Matched abc123 with left over !.
```
