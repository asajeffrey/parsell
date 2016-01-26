# parsimonious: a parser combinator library for Rust

The goal of this project is to implement a parser combinator library that:

* Supports streaming input
* Does as little buffering or copying as possible
* Does not use dynamic method dispatch

It is based on "Monadic Parsing in Haskell" by Hutton and Meijer, JFP 8(4) pp. 437-444.