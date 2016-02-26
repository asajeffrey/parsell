//! Parsell: an LL(1) streaming parser combinator library for Rust
//!
//! The goal of this library is to provide parser combinators that:
//!
//! * are optimized for LL(1) grammars,
//! * support streaming input,
//! * do as little buffering or copying as possible, and
//! * do as little dynamic method dispatch as possible.
//!
//! It is based on:
//!
//! * [Monadic Parsing in Haskell](http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf)
//!   by G. Hutton and E. Meijer, JFP 8(4) pp. 437-444,
//! * [Nom, eating data byte by byte](https://github.com/Geal/nom) by G. Couprie.
//!
//! [Video](https://air.mozilla.org/bay-area-rust-meetup-february-2016/) |
//! [Slides](http://asajeffrey.github.io/parsell/doc/talks/sf-rust-2016-02-18/) |
//! [Repo](https://github.com/asajeffrey/parsell) |
//! [Crate](https://crates.io/crates/parsell) |
//! [CI](https://travis-ci.org/asajeffrey/parsell)

#![feature(unboxed_closures)]

use self::ParseResult::{Done, Continue};

use std::borrow::Cow;
use std::str::Chars;
use std::iter::Peekable;
use std::fmt::{Debug, Formatter};

pub mod impls;

// ----------- Types for parsers ------------

/// A trait for stateful parsers.
///
/// Stateful parsers are typically constructed by calling an `init` method of a stateless parser,
/// for example:
///
/// ```
/// # use parsell::{character,Parser,Uncommitted,UncommittedStr,Committed,Stateful};
/// # use parsell::ParseResult::{Continue,Done};
/// let stateless = character(char::is_alphanumeric).star(String::new);
/// match stateless.init_str("abc").unwrap() {
///    Continue(stateful) => (),
///    _ => panic!("Can't happen"),
/// }
/// ```
///
/// Here, `stateless` is a `Committed<char, Chars<'a>>`, and `stateful` is a `Stateful<char, Chars<'a>>`.
///
/// The reason for distinguishing between stateful and stateless parsers is that
/// stateless parsers are usually copyable, whereas stateful parsers are usually not
/// (they may, for example, have created and partially filled some buffers).
/// Copying parsers is quite common, for example:
///
/// ```
/// # use parsell::{character,CHARACTER,Uncommitted,UncommittedStr,Parser,Committed,Stateful};
/// # use parsell::ParseResult::Done;
/// fn mk_err(_: Option<char>) -> Result<char,String> { Err(String::from("Expecting a digit")) }
/// let DIGIT = character(char::is_numeric).map(Ok).or_else(CHARACTER.map(mk_err));
/// let TWO_DIGITS = DIGIT.try_and_then_try(DIGIT);
/// match TWO_DIGITS.init_str("123").unwrap() {
///    Done(result) => assert_eq!(result, Ok(('1','2'))),
///    _ => panic!("Can't happen"),
/// }
/// ```

pub trait Stateful<Input, Output> 
{
    
    /// Provides data to the parser.
    ///
    /// If `parser: Stateful<Input, Output>` and `data: Input`, then `parser.more(&mut data)` either:
    ///
    /// * returns `Done(result)` where and `result: Output` is the parsed output, or
    /// * returns `Continue(parsing)` where `parsing: Self` is the new state of the parser.
    ///
    /// For example:
    
    /// ```
    /// # use parsell::{character,Parser,Uncommitted,Committed,Stateful};
    /// # use parsell::ParseResult::{Continue,Done};
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// let data1 = "ab";
    /// let data2 = "cd";
    /// let data3 = "ef!";
    /// match parser.init(&mut data1.chars()).unwrap() {
    ///     Continue(stateful) => match stateful.more(&mut data2.chars()) { 
    ///         Continue(stateful) => match stateful.more(&mut data3.chars()) { 
    ///             Done(result) => assert_eq!(result, "abcdef"),
    ///             _ => panic!("can't happen"),
    ///         },
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```
    ///
    /// Note that `parser.parse(data)` consumes the `parser`, but borrows the `data`
    /// mutably.

    fn more(self, data: &mut Input) -> ParseResult<Self, Output>
        where Self: Sized;

    /// Tells the parser that it will not receive any more data.
    ///
    /// If `parser: Stateful<Input, Output>`, then `parser.done()` returns a result of type `Output`
    /// for example:
    ///
    /// ```
    /// # use parsell::{character,Parser,Uncommitted,Committed,Stateful};
    /// # use parsell::ParseResult::{Continue,Done};
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// let data1 = "ab";
    /// let data2 = "cd";
    /// let data3 = "ef";
    /// match parser.init(&mut data1.chars()).unwrap() {
    ///     Continue(stateful) => match stateful.more(&mut data2.chars()) { 
    ///         Continue(stateful) => assert_eq!(stateful.last(&mut data3.chars()), "abcdef"),
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```
    ///
    /// Note that `parser.done()` consumes the `parser`. In particular,
    /// the `parser` is no longer available, so the following does not typecheck:
    ///
    /// ```text
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// match parser.init_str("abc").unwrap() {
    ///     Continue(parsing) => {
    ///         parsing.done();
    ///         parsing.more_str("def!");
    ///     }
    /// }
    /// ```
    ///
    /// This helps with parser safety, as it stops a client from calling `more` after
    /// `done`.

    fn done(self) -> Output
        where Self: Sized;

    /// Provides the last data to the parser.
    ///
    /// If `parser: Stateful<Input, Output>` and `data: Input`, then `parser.last(&mut data)`
    /// calls `parser.more(&mut data)`, then calls `done()` if the parser continues.
    
    fn last(self, data: &mut Input) -> Output
        where Self: Sized
    {
        match self.more(data) {
            Continue(parsing) => parsing.done(),
            Done(result) => result,
        }
    }

}

/// A trait for stateful string parsers.

pub trait StatefulStr<'a, Output>: Stateful<Chars<'a>, Output> {

    /// Provides a string to the parser.
    ///
    /// If `parser: Stateful<Chars<'a>, Output>` and `data: &'a str`, then `parser.more_str(data)`
    /// is short-hand for `parser.more(&mut data.chars())`.
    ///
    /// For example:
    ///
    /// ```
    /// # use parsell::{character,Parser,Uncommitted,UncommittedStr,Committed,Stateful,StatefulStr};
    /// # use parsell::ParseResult::{Continue,Done};
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// match parser.init_str("ab").unwrap() {
    ///     Continue(stateful) => match stateful.more_str("cd") { 
    ///         Continue(stateful) => match stateful.more_str("ef!") { 
    ///             Done(result) => assert_eq!(result, "abcdef"),
    ///             _ => panic!("can't happen"),
    ///         },
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```

    fn more_str(self, string: &'a str) -> ParseResult<Self, Output>
        where Self: Sized,
    {
        self.more(&mut string.chars())
    }

    /// Provides the last string to the parser.
    ///
    /// If `parser: Stateful<Chars<'a>, Output>` and `data: &'a str`, then `parser.last_str(data)`
    /// is short-hand for `parser.last(&mut data.chars())`.
    ///
    /// For example:
    ///
    /// ```
    /// # use parsell::{character,Parser,Uncommitted,UncommittedStr,Committed,Stateful,StatefulStr};
    /// # use parsell::ParseResult::{Continue,Done};
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// match parser.init_str("ab").unwrap() {
    ///     Continue(parsing) => match parsing.more_str("cd") {
    ///         Continue(parsing) => assert_eq!(parsing.last_str("ef"),"abcdef"),
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```

    fn last_str(self, string: &'a str) -> Output
        where Self: Sized,
    {
        self.last(&mut string.chars())
    }

}

impl<'a, Output, P> StatefulStr<'a, Output> for P where P: Stateful<Chars<'a>, Output> {}

/// The result of parsing
#[derive(Copy, Clone)]
pub enum ParseResult<State, Output> {

    /// The parse is finished.
    Done(Output),
    
    /// The parse can continue.
    Continue(State),

}

// Implement Debug for ParseResult<P, S> without requiring P: Debug

impl<P, S> Debug for ParseResult<P, S>
    where S: Debug,
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        match self {
            &Done(ref result) => write!(fmt, "Done({:?})", result),
            &Continue(_) => write!(fmt, "Continue(...)"),
        }
    }
}

impl<P,S> PartialEq for ParseResult<P, S> where S: PartialEq {
    fn eq(&self, other: &ParseResult<P, S>) -> bool {
        match (self, other) {
            (&Done(ref result1), &Done(ref result2)) => (result1 == result2),
            _ => false,
        }
    }
}

/// A trait for stateless parsers.
///
/// Parsers are implemented either as committed parsers, which cannot backtrack,
/// or uncommitted parsers, which can backtrack on their first token of input.
/// For example `character(char::is_alphabetic)` is uncommitted because
/// it will backtrack on any non-alphabetic character, but
/// `CHARACTER` is not, because it will produce `None` rather than backtracking.

pub trait Parser {

    /// Choice between parsers
    fn or_else<P>(self, other: P) -> impls::OrElse<Self, P>
        where Self: Sized,
              P: Parser,
    {
        impls::OrElse::new(self, other)
    }

    /// Sequencing with a committed parser
    fn and_then<P>(self, other: P) -> impls::AndThen<Self, P>
        where Self: Sized,
              P: Parser,
    {
        impls::AndThen::new(self, other)
    }

    /// Sequencing with a committed parser (bubble any errors from this parser).
    fn try_and_then<P>(self, other: P) -> impls::Map<impls::AndThen<Self, P>, impls::TryZip>
        where Self: Sized,
              P: Parser,
    {
        self.and_then(other).map(impls::TryZip)
    }

    /// Sequencing with a committed parser (bubble any errors from that parser).
    fn and_then_try<P>(self, other: P) -> impls::Map<impls::AndThen<Self, P>, impls::ZipTry>
        where Self: Sized,
              P: Parser,
    {
        self.and_then(other).map(impls::ZipTry)
    }

    /// Sequencing with a committed parser (bubble any errors from either parser).
    fn try_and_then_try<P>(self, other: P) -> impls::Map<impls::AndThen<Self, P>, impls::TryZipTry>
        where Self: Sized,
              P: Parser,
    {
        self.and_then(other).map(impls::TryZipTry)
    }

    /// Iterate one or more times (returns an uncommitted parser).
    fn plus<F>(self, factory: F) -> impls::Plus<Self, F>
        where Self: Sized,
              F: Factory,
    {
        impls::Plus::new(self, factory)
    }

    /// Iterate zero or more times (returns a committed parser).
    fn star<F>(self, factory: F) -> impls::Star<Self, F>
        where Self: Sized,
              F: Factory,
    {
        impls::Star::new(self, factory)
    }

    /// Apply a function to the result
    fn map<F>(self, f: F) -> impls::Map<Self, F>
        where Self: Sized,
    {
        impls::Map::new(self, f)
    }

    /// Apply a 2-arguent function to the result
    fn map2<F>(self, f: F) -> impls::Map<Self, impls::Function2<F>>
        where Self: Sized,
    {
        impls::Map::new(self, impls::Function2::new(f))
    }

    /// Apply a 3-arguent function to the result
    fn map3<F>(self, f: F) -> impls::Map<Self, impls::Function3<F>>
        where Self: Sized,
    {
        impls::Map::new(self, impls::Function3::new(f))
    }

    /// Apply a 4-arguent function to the result
    fn map4<F>(self, f: F) -> impls::Map<Self, impls::Function4<F>>
        where Self: Sized,
    {
        impls::Map::new(self, impls::Function4::new(f))
    }

    /// Apply a 5-arguent function to the result
    fn map5<F>(self, f: F) -> impls::Map<Self, impls::Function5<F>>
        where Self: Sized,
    {
        impls::Map::new(self, impls::Function5::new(f))
    }

    /// Apply a function to the result (bubble any errors).
    fn try_map<F>(self, f: F) -> impls::Map<Self, impls::Try<F>>
        where Self: Sized
    {
        self.map(impls::Try::new(f))
    }

    /// Apply a 2-argument function to the result (bubble any errors).
    fn try_map2<F>(self, f: F) -> impls::Map<Self, impls::Try<impls::Function2<F>>>
        where Self: Sized
    {
        self.try_map(impls::Function2::new(f))
    }

    /// Apply a 3-argument function to the result (bubble any errors).
    fn try_map3<F>(self, f: F) -> impls::Map<Self, impls::Try<impls::Function3<F>>>
        where Self: Sized
    {
        self.try_map(impls::Function3::new(f))
    }

    /// Apply a 4-argument function to the result (bubble any errors).
    fn try_map4<F>(self, f: F) -> impls::Map<Self, impls::Try<impls::Function4<F>>>
        where Self: Sized
    {
        self.try_map(impls::Function4::new(f))
    }

    /// Apply a 5-argument function to the result (bubble any errors).
    fn try_map5<F>(self, f: F) -> impls::Map<Self, impls::Try<impls::Function5<F>>>
        where Self: Sized
    {
        self.try_map(impls::Function5::new(f))
    }

    /// Sequencing, discard the output of the first parse
    fn discard_and_then<P>(self, other: P) -> impls::Map<impls::AndThen<Self, P>, impls::Second>
        where Self: Sized,
              P: Parser,
    {
        self.and_then(other).map(impls::Second)
    }

    /// Sequencing, discard the output of the second parse
    fn and_then_discard<P>(self, other: P) -> impls::Map<impls::AndThen<Self, P>, impls::First>
        where Self: Sized,
              P: Parser,
    {
        self.and_then(other).map(impls::First)
    }

    /// Sequencing, discard the output of the first parse, bubble errors from the first parser
    fn try_discard_and_then<P>(self, other: P) -> impls::Map<impls::Map<impls::AndThen<Self, P>, impls::TryZip>, impls::Try<impls::Second>>
        where Self: Sized,
              P: Parser,
    {
        self.try_and_then(other).try_map(impls::Second)
    }

    /// Sequencing, discard the output of the second parse, bubble errors from the second parser
    fn and_then_try_discard<P>(self, other: P) -> impls::Map<impls::Map<impls::AndThen<Self, P>, impls::ZipTry>, impls::Try<impls::First>>
        where Self: Sized,
              P: Parser,
    {
        self.and_then_try(other).try_map(impls::First)
    }

    /// Sequencing, discard the output of the first parse, bubble errors from either parser
    fn try_discard_and_then_try<P>(self, other: P) -> impls::Map<impls::Map<impls::AndThen<Self, P>, impls::TryZipTry>, impls::Try<impls::Second>>
        where Self: Sized,
              P: Parser,
    {
        self.try_and_then_try(other).try_map(impls::Second)
    }

    /// Sequencing, discard the output of the second parse, bubble errors from either parser
    fn try_and_then_try_discard<P>(self, other: P) -> impls::Map<impls::Map<impls::AndThen<Self, P>, impls::TryZipTry>, impls::Try<impls::First>>
        where Self: Sized,
              P: Parser,
    {
        self.try_and_then_try(other).try_map(impls::First)
    }

    /// Optional parse
    fn opt(self) -> impls::Opt<Self>
        where Self: Sized,
    {
        impls::Opt::new(self)
    }
    
    /// Discard the output
    fn discard(self) -> impls::Map<Self, impls::Discard>
        where Self: Sized,
    {
        self.map(impls::Discard)
    }
    
//     // /// Take the results of iterating this parser, and feed it into another parser.
//     // fn pipe<P>(self, other: P) -> impls::PipeParser<Self, P>
//     //     where Self: Sized
//     // {
//     //     impls::PipeParser::new(self, other)
//     // }

    // Box up this parser
    fn boxed<F>(self, f: F) -> impls::Boxed<Self, F>
        where Self: Sized
    {
        impls::Boxed::new(self, f)
    }

//     /// A parser which produces its input.
//     ///
//     /// This does its best to avoid having to buffer the input. The result of a buffered parser
//     /// may be borrowed (because no buffering was required) or owned (because buffering was required).
//     /// Buffering is required in the case that the input was provided in chunks, rather than
//     /// contiguously. For example:
//     ///
//     /// ```
//     /// # use parsell::{character,Parser,Uncommitted,Stateful};
//     /// # use parsell::ParseResult::{Done,Continue};
//     /// # use std::borrow::Cow::{Borrowed,Owned};
//     /// fn ignore() {}
//     /// let parser = character(char::is_alphabetic).plus(ignore).buffer();
//     /// match parser.init(&mut "abc!".chars()).unwrap() {
//     ///     Done(Borrowed(result)) => assert_eq!(result,"abc"),
//     ///     _ => panic!("can't happen"),
//     /// }
//     /// match parser.init(&mut "abc".chars()).unwrap() {
//     ///     Continue(parsing) => match parsing.more(&mut "def!".chars()) {
//     ///         Done(Owned(result)) => assert_eq!(result,"abcdef"),
//     ///         _ => panic!("can't happen"),
//     ///     },
//     ///     _ => panic!("can't happen"),
//     /// }
//     /// ```
//     fn buffer(self) -> impls::Buffered<Self>
//         where Self: Sized
//     {
//         impls::Buffered::new(self)
//     }

}

/// A trait for committed parsers.
///
/// A parser is committed if it is guaranteed only to backtrack on empty input.
/// Committed parsers are typically constructed by calling the methods of the library,
/// for example:
///
// /// ```
// /// # use parsell::{character,Parser,Uncommitted};
// /// let parser = character(char::is_alphanumeric).star(String::new);
// /// ```
///
/// Here, `parser` is a `Committed<Chars<'a>, String>`.
///
/// The reason for distinguishing between committed and uncommitted parsers
/// is that the library is designed for LL(1) grammars, that only use one token
/// of lookahead. This means that the sequence of two parsers
/// `p.and_then(q)` is only well-defined when `q` is committed,
/// since if `p` commits, then `q` cannot backtrack.
///
/// Semantically, a parser with input *S* and output *T* is a partial function *S\* → T*
/// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain)
/// and non-empty.

pub trait Committed<State, Input, Output>: Uncommitted<State, Input, Output>
{

    /// Parse an EOF.
    fn empty(&self) -> Output;
    
}

/// A trait for uncommitted parsers.
///
/// An uncommitted parser can decide based on the first token of input whether
/// it will commit to parsing, or immediately backtrack and try another option.
///
/// The advantage of uncommitted parsers over committed parsers is they support choice:
/// `p.or_else(q)` will try `p`, and commit if it commits, but if it backtracks
/// will then try `q`. For example:
///
// /// ```
// /// # use parsell::{character,CHARACTER,Parser,Uncommitted,UncommittedStr,Committed,Stateful};
// /// # use parsell::ParseResult::Done;
// /// fn default(_: Option<char>) -> String { String::from("?") }
// /// let parser =
// ///    character(char::is_numeric).plus(String::new)
// ///        .or_else(character(char::is_alphabetic).plus(String::new))
// ///        .or_else(CHARACTER.map(default));
// /// match parser.init_str("123abc").unwrap() {
// ///    Done(result) => assert_eq!(result, "123"),
// ///    _ => panic!("Can't happen"),
// /// }
// /// match parser.init_str("abc123").unwrap() {
// ///    Done(result) => assert_eq!(result, "abc"),
// ///    _ => panic!("Can't happen"),
// /// }
// /// match parser.init_str("!@#").unwrap() {
// ///    Done(result) => assert_eq!(result, "?"),
// ///    _ => panic!("Can't happen"),
// /// }
// /// ```
///
/// Semantically, a parser with input *S* and output *T* is a partial function *S\+ → T*
/// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain).

pub trait Uncommitted<State, Input, Output>
{

    /// Parse a string of data.
    fn init(&self, data: &mut Input) -> Option<ParseResult<State, Output>>;

}

/// A trait for parsers which can infer their output and state

pub trait Infer<Input> {
    type Output;
    type State;
}

/// A trait for uncommitted parsers that know their state

pub trait UncommittedInfer<Input>: Infer<Input> + Uncommitted<<Self as Infer<Input>>::State, Input, <Self as Infer<Input>>::Output>
{
    fn init_infer(&self, data: &mut Input) -> Option<ParseResult<Self::State, Self::Output>>
    {
        self.init(data)
    }
}

impl<Input, P> UncommittedInfer<Input> for P
    where P: Infer<Input> + Uncommitted<<P as Infer<Input>>::State, Input, <P as Infer<Input>>::Output>
{
}

/// A trait for uncommitted string parsers.

pub trait UncommittedStr<'a>: Infer<Chars<'a>> + Uncommitted<<Self as Infer<Chars<'a>>>::State, Chars<'a>, <Self as Infer<Chars<'a>>>::Output>
{

    /// Provides string data to the parser.
    ///
    /// If `parser: Uncommitted<char, Chars<'a>>` and `data: &'a str`, then `parser.init_str(data)`
    /// is short-hand for `parser.init(&mut data.chars())`.
    ///
    /// For example:
    ///
    // /// ```
    // /// # use parsell::{character,Parser,Uncommitted,UncommittedStr,Committed,Stateful,StatefulStr};
    // /// # use parsell::ParseResult::{Continue,Done};
    // /// let parser = character(char::is_alphabetic).star(String::new);
    // /// match parser.init_str("ab").unwrap() {
    // ///     Continue(stateful) => match stateful.more_str("cd") { 
    // ///         Continue(stateful) => match stateful.more_str("ef!") { 
    // ///             Done(result) => assert_eq!(result, "abcdef"),
    // ///             _ => panic!("can't happen"),
    // ///         },
    // ///         _ => panic!("can't happen"),
    // ///     },
    // ///     _ => panic!("can't happen"),
    // /// }
    // /// ```

    fn init_str(&self, string: &'a str) -> Option<ParseResult<Self::State, Self::Output>>
    {
        self.init(&mut string.chars())
    }

}

impl<'a, P> UncommittedStr<'a> for P
    where P: Infer<Chars<'a>> + Uncommitted<<P as Infer<Chars<'a>>>::State, Chars<'a>, <P as Infer<Chars<'a>>>::Output>
{
}

/// A trait for boxable parsers.
///
/// Regular languages can be parsed in constant memory, so do not require any heap allocation (other than
/// the heap allocation peformed by user code such as creating buffers). Context-free languages require
/// allocating unbounded memory. In order to support streaming input, the state of the parser must be
/// saved on the heap, and restored when more input arrives.
///
/// In Rust, heap-allocated data is often kept in a `Box<T>`, where `T` is a trait. In the case
/// of parsers, the library needs to save and restore a stateful parser, for which the obvious
/// type is `Box<Stateful<Ch, Str, Output=T>`. There are two issues with this...
///
/// Firstly, the lifetimes mentioned in the type of the parser may change over time.
/// For example, the program:
///
/// ```text
/// let this: &'a str = ...;
/// let that: &'b str = ...;
/// let parser = character(char::is_alphanumeric).star(ignore).buffer();
/// match parser.init_str(this).unwrap() {
///     Continue(stateful) => {
///         let boxed: Box<Stateful<char, Chars<'a>, Output=Cow<'a, str>>> = Box::new(stateful);
///         match boxed.more_str(that) {
///             Done(result: Cow<'b,str>) => ...
/// ```
///
/// does not typecheck, because the type of `boxed` is fixed as containing parsers for input `&'a str`,
/// but it was fed input of type `&'b str`. To fix this, we change the type of the box to be
/// polymorphic in the lifetime of the parser:
///
/// ```text
/// let this: &'a str = ...;
/// let that: &'b str = ...;
/// let parser = character(char::is_alphanumeric).star(ignore).buffer();
/// match parser.init_str(this).unwrap() {
///     Continue(stateful) => {
///         let boxed: Box<for<'c> Stateful<char, Chars<'c>, Output=Cow<'c, str>>> = Box::new(stateful);
///         match boxed.more_str(that) {
///             Done(result: Cow<'b,str>) => ...
/// ```
///
/// Secondly, the `Stateful` trait is not
/// [object-safe](https://doc.rust-lang.org/book/trait-objects.html#object-safety),
/// so cannot be boxed and unboxed safely. In order to address this, there is a trait
/// `Boxable<Ch, Str>`, which represents stateful parsers, but is object-safe
/// and so can be boxed and unboxed safely.
///
/// The type `Box<Boxable<Ch, Str>>` implements the trait
/// `Stateful<Ch, Str>`, so boxes can be used as parsers,
/// which allows stateful parsers to heap-allocate their state.
///
/// Boxable parsers are usually used in recursive-descent parsing,
/// for context-free grammars that cannot be parsed as a regular language.
/// For example, consider a simple type for trees:
///
/// ```
/// struct Tree(Vec<Tree>);
/// ```
///
/// which can be parsed from a well-nested sequence of parentheses, for example
/// `(()())` can be parsed as `Tree(vec![Tree(vec![]),Tree(vec![])])`.
/// The desired implementation is:
///
/// ```text
/// fn is_lparen(ch: char) -> bool { ch == '(' }
/// fn is_rparen(ch: char) -> bool { ch == ')' }
/// fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
/// fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
/// fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
/// fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Tree { Tree(children) }
/// let LPAREN = character(is_lparen);
/// let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
/// let TREE = LPAREN
///      .and_then_try(TREE.star(mk_vec))
///      .try_and_then_try(RPAREN)
///      .try_map3(mk_tree);
/// ```
///
/// but this doesn't work because it gives the definition of `TREE` in terms of itself,
/// and Rust doesn't allow this kind of cycle.
///
/// Instead, the solution is to define a struct `TreeParser`, and then implement `Uncommitted<char, Chars<'a>>`
/// for it. The type of the state of a `TreeParser` is a box containing an appropriate
/// `BoxableParserState` trait:
///
// /// ```
// /// # use std::str::Chars;
// /// # use parsell::{Boxable};
// /// # struct Tree(Vec<Tree>);
// /// type TreeParserState = Box<for<'b> Boxable<char, Chars<'b>, Output=Result<Tree, String>>>;
// /// ```
// ///
// /// The implementation of `Uncommitted<char, Chars<'b>>` for `TreeParser` is mostly straightfoward:
// ///
// /// ```
// /// # use std::str::Chars;
// /// # use parsell::{character,CHARACTER,Parser,Uncommitted,Committed,Boxable,Stateful,ParseResult,StaticMarker};
// /// # use parsell::ParseResult::{Done,Continue};
// /// # #[derive(Eq,PartialEq,Clone,Debug)]
// /// struct Tree(Vec<Tree>);
// /// impl StaticMarker for Tree {}
// /// # type TreeParserState = Box<for<'a> Boxable<char, Chars<'a>, Output=Result<Tree, String>>>;
// /// # fn is_lparen(ch: char) -> bool { ch == '(' }
// /// # fn is_rparen(ch: char) -> bool { ch == ')' }
// /// # fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
// /// # fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
// /// # fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
// /// # fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Tree { Tree(children) }
// /// # fn mk_box<P>(state: P) -> TreeParserState
// /// #     where P: 'static+for<'a> Boxable<char, Chars<'a>, Output=Result<Tree,String>>
// /// # {
// /// #     Box::new(state)
// /// # }
// /// # #[derive(Copy,Clone,Debug)]
// /// struct TreeParser;
// /// impl Parser for TreeParser {}
// /// impl<'a> Uncommitted<char, Chars<'a>> for TreeParser {
// ///     type Output = Result<Tree, String>;
// ///     type State = TreeParserState;
// ///     fn init(&self, data: &mut Chars<'a>) -> Option<ParseResult<Self::State, Self::Output>> {
// ///         // ... parser goes here...`
// /// #       let LPAREN = character(is_lparen);
// /// #       let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
// /// #       let parser = LPAREN
// /// #           .and_then_try(TreeParser.star(mk_vec))
// /// #           .try_and_then_try(RPAREN)
// /// #           .try_map3(mk_tree)
// /// #           .boxed(mk_box);
// /// #       parser.init(data)
// ///     }
// /// }
// /// ```
// ///
// /// The important thing is that the definiton of `parse` can make use of `TREE`, so the parser can call itself
// /// recursively, then box up the result state. Boxing up the state makes use of a method `parser.box(mk_box)`
// /// where `mk_box` is a function that boxes up boxable state:
// ///
// /// ```
// /// # use std::str::Chars;
// /// # use parsell::{character,CHARACTER,Parser,Uncommitted,UncommittedStr,Committed,Boxable,Stateful,StatefulStr,ParseResult,StaticMarker};
// /// # use parsell::ParseResult::{Done,Continue};
// /// # #[derive(Eq,PartialEq,Clone,Debug)]
// /// # struct Tree(Vec<Tree>);
// /// # impl StaticMarker for Tree {}
// /// # type TreeParserState = Box<for<'a> Boxable<char, Chars<'a>, Output=Result<Tree, String>>>;
// /// fn is_lparen(ch: char) -> bool { ch == '(' }
// /// fn is_rparen(ch: char) -> bool { ch == ')' }
// /// fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
// /// fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
// /// fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
// /// fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Tree { Tree(children) }
// /// fn mk_box<P>(state: P) -> TreeParserState
// ///     where P: 'static+for<'a> Boxable<char, Chars<'a>, Output=Result<Tree,String>>
// /// {
// ///     Box::new(state)
// /// }
// /// # #[derive(Copy,Clone,Debug)]
// /// struct TreeParser;
// /// impl Parser for TreeParser {}
// /// impl<'a> Uncommitted<char, Chars<'a>> for TreeParser {
// ///     type Output = Result<Tree, String>;
// ///     type State = TreeParserState;
// ///     fn init(&self, data: &mut Chars<'a>) -> Option<ParseResult<Self::State, Self::Output>> {
// ///         let LPAREN = character(is_lparen);
// ///         let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
// ///         let parser = LPAREN
// ///             .and_then_try(TreeParser.star(mk_vec))
// ///             .try_and_then_try(RPAREN)
// ///             .try_map3(mk_tree);
// ///         parser.boxed(mk_box).init(data)
// ///     }
// /// }
// /// let TREE = TreeParser;
// /// match TREE.init_str("((").unwrap() {
// ///     Continue(parsing) => match parsing.more_str(")())") {
// ///         Done(result) => assert_eq!(result, Ok(Tree(vec![Tree(vec![]),Tree(vec![])]))),
// ///          _ => panic!("Can't happen"),
// ///     },
// ///     _ => panic!("Can't happen"),
// /// }
// /// ```
// ///
// /// The reason for making `Boxable<S>` a different trait from `Stateful<S>`
// /// is that it provides weaker safety guarantees. `Stateful<S>` enforces that
// /// clients cannot call `parse` after `done`, but `Boxable<S>` does not.

pub trait Boxable<Input, Output> 
{
    fn more_boxable(&mut self, data: &mut Input) -> ParseResult<(), Output>;
    fn done_boxable(&mut self) -> Output;
}

/// A trait for one-argument functions.
///
/// This trait is just the same as `Fn(T) -> U`, but can be implemented by a struct.
/// This is useful, as it allows the function type to be named, for example
///
/// ```
/// # use parsell::{Function,character};
/// # use parsell::impls::{Character};
/// struct AlphaNumeric;
/// impl Function<char> for AlphaNumeric {
///     type Output = bool;
///     fn apply(&self, arg: char) -> bool { arg.is_alphanumeric() }
/// }
/// let parser: Character<AlphaNumeric> =
///     character(AlphaNumeric);
/// ```
///
/// Here, we can name the type of the parser `Character<AlphaNumeric>`,
/// which would not be possible if `character` took its argument as a `Fn(T) -> U`,
/// since `typeof` is not implemented in Rust.
/// At some point, Rust will probably get abstract return types,
/// at which point the main need for this type will go away.

pub trait Function<S> {
    type Output;
    fn apply(&self, arg: S) -> Self::Output;
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<F, S> Function<S> for F where F: Fn<(S, )>
{
    type Output = F::Output;
    fn apply(&self, arg: S) -> F::Output {
        self(arg)
    }
}

/// A trait for factories.

pub trait Factory {
    type Output;
    fn build(&self) -> Self::Output;
}

impl<F, T> Factory for F where F: Fn() -> T
{
    type Output = T;
    fn build(&self) -> T {
        self()
    }
}

/// A trait for consumers of data, typically buffers.
///
/// # Examples
///
/// `String` is a consumer of `&str` and of `char`.
///
/// ```
/// # use parsell::Consumer;
/// let mut buffer = String::new();
/// buffer.accept("abc");
/// buffer.accept('d');
/// assert_eq!(buffer,"abcd");
/// ```
///
/// `Vec<T>` is a consumer of `&[T]` when `T` is `Clone`, and of `T`.
///
/// ```
/// # use parsell::Consumer;
/// let mut buffer = Vec::new();
/// buffer.accept(&[1,2,3][..]);
/// buffer.accept(4);
/// assert_eq!(buffer,&[1,2,3,4]);
/// ```
///
/// The unit type `()` is a trivial consumer that discards data.
///
/// ```
/// # use parsell::Consumer;
/// let mut discarder = ();
/// discarder.accept("this");
/// discarder.accept(4);
/// assert_eq!(discarder,());
/// ```

pub trait Consumer<T> {
    /// Accepts data.
    fn accept(&mut self, value: T);
}

impl<T> Consumer<T> for () {
    fn accept(&mut self, _: T) {}
}

impl Consumer<String> for String {
    fn accept(&mut self, arg: String) {
        self.push_str(&*arg);
    }
}

impl<'a> Consumer<&'a str> for String {
    fn accept(&mut self, arg: &'a str) {
        self.push_str(arg);
    }
}

impl Consumer<char> for String {
    fn accept(&mut self, x: char) {
        self.push(x);
    }
}

impl<'a, T> Consumer<&'a [T]> for Vec<T> where T: Clone
{
    fn accept(&mut self, arg: &'a [T]) {
        self.extend(arg.iter().cloned());
    }
}

impl<T> Consumer<T> for Vec<T> {
    fn accept(&mut self, x: T) {
        self.push(x);
    }
}

impl<C, T, E> Consumer<Result<T, E>> for Result<C, E> where C: Consumer<T>
{
    fn accept(&mut self, value: Result<T, E>) {
        let err = match *self {
            Err(_) => return,
            Ok(ref mut consumer) => {
                match value {
                    Err(err) => err,
                    Ok(value) => return consumer.accept(value),
                }
            }
        };
        *self = Err(err);
    }
}

// /// A trait for subtyping

// pub trait Upcast<T:?Sized> {
//     fn upcast(self) -> T where Self: Sized;
// }

// impl<'a, T: ?Sized> Upcast<Cow<'a, T>> for Cow<'static, T>
//     where T: ToOwned,
// {
//     fn upcast(self) -> Cow<'a, T> { self }
// }

// impl<S1, S2, T1, T2> Upcast<(T1, T2)> for (S1,S2)
//     where S1: Upcast<T1>,
//           S2: Upcast<T2>,
// {
//     fn upcast(self) -> (T1, T2) { (self.0.upcast(), self.1.upcast()) }
// }

// impl<S, T> Upcast<Option<T>> for Option<S>
//     where S: Upcast<T>,
// {
//     fn upcast(self) -> Option<T> { self.map(Upcast::upcast) }
// }

// impl<S, T, D, E> Upcast<Result<T,E>> for Result<S,D>
//     where S: Upcast<T>,
//           D: Upcast<E>,
// {
//     fn upcast(self) -> Result<T,E> { self.map(Upcast::upcast).map_err(Upcast::upcast) }
// }

// /// A trait for data which can be saved to and restored from long-lived state.
// ///
// /// The canonical example of this trait is `Cow<'a,T>` which can be saved to
// /// and restored from `Cow<'static,T>` when `T` is static.

// pub trait ToStatic {
//     type Static: 'static + Upcast<Self>;
//     fn to_static(self) -> Self::Static where Self: Sized;
// }

// impl<'a, T: ?Sized> ToStatic for Cow<'a, T>
//     where T: 'static + ToOwned
// {
//     type Static = Cow<'static, T>;
//     fn to_static(self) -> Self::Static { Cow::Owned(self.into_owned()) }
// }

// impl<T, U> ToStatic for (T, U)
//     where T: ToStatic,
//           U: ToStatic
// {
//     type Static = (T::Static, U::Static);
//     fn to_static(self) -> Self::Static { (self.0.to_static(), self.1.to_static()) }
// }

// impl<T> ToStatic for Option<T>
//     where T: ToStatic
// {
//     type Static = Option<T::Static>;
//     fn to_static(self) -> Self::Static { self.map(ToStatic::to_static) }
// }

// impl<T,E> ToStatic for Result<T,E> where T: ToStatic, E: ToStatic {
//     type Static = Result<T::Static,E::Static>;
//     fn to_static(self) -> Self::Static { self.map(ToStatic::to_static).map_err(ToStatic::to_static) }
// }

// /// A marker trait for static data.
// ///
// /// This trait is a quick way to implment `ToStatic` as a no-op.

// pub trait StaticMarker {}

// impl<T> Upcast<T> for T where T: StaticMarker {
//     fn upcast(self) -> T { self }
// }

// impl<T> ToStatic for T where T: 'static + StaticMarker {
//     type Static = T;
//     fn to_static(self) -> T { self }
// }

// impl StaticMarker for usize {}
// impl StaticMarker for u8 {}
// impl StaticMarker for u16 {}
// impl StaticMarker for u32 {}
// impl StaticMarker for u64 {}
// impl StaticMarker for isize {}
// impl StaticMarker for i8 {}
// impl StaticMarker for i16 {}
// impl StaticMarker for i32 {}
// impl StaticMarker for i64 {}
// impl StaticMarker for () {}
// impl StaticMarker for bool {}
// impl StaticMarker for char {}
// impl StaticMarker for String {}
// impl<T> StaticMarker for Vec<T> where T: 'static {}

/// A trait for peekable iterators

struct ByRef<F>(F);

impl<'a, T, F> Function<&'a T> for ByRef<F> where
    F: Function<T>,
    T: Copy,
{
    type Output = F::Output;
    fn apply(&self, arg: &'a T) -> F::Output { self.0.apply(*arg) }
}

pub trait PeekableIterator: Iterator {

    fn is_empty(&mut self) -> bool;

    fn next_if_ref<F>(&mut self, f: F) -> Option<Self::Item>
        where F: for<'a> Function<&'a Self::Item, Output = bool>;

    fn next_if<F>(&mut self, f: F) -> Option<Self::Item>
        where F: Function<Self::Item, Output = bool>,
              Self::Item: Copy,
    {
        self.next_if_ref(ByRef(f))
    }

}

impl<I> PeekableIterator for Peekable<I>
    where I: Iterator
{
    fn is_empty(&mut self) -> bool {
        self.peek().is_none()
    }
        
    fn next_if_ref<F>(&mut self, f: F) -> Option<Self::Item>
        where F: for<'a> Function<&'a Self::Item, Output = bool>
    {
        match self.peek() {
            Some(ref item) if f.apply(item) => (),
            _ => return None,
        };
        self.next()
    }
}

impl<'a> PeekableIterator for Chars<'a>
{
    fn is_empty(&mut self) -> bool {
        self.as_str().is_empty()
    }

    fn next_if_ref<F>(&mut self, f: F) -> Option<char>
        where F: for<'b> Function<&'b char, Output = bool>
    {
        match self.as_str().chars().next() {
            Some(ref ch) if f.apply(ch) => self.next(),
            _ => None
        }        
    }
}

/// An uncommitted parser that reads one character.
///
/// The parser `character(f)` reads one character `ch` from the input,
/// if `f(ch)` is `true` then it commits and the result is `ch`,
/// otherwise it backtracks.
///
/// This requires characters to be copyable.

pub fn character<F>(f: F) -> impls::Character<F> {
    impls::Character::new(f)
}

/// An uncommitted parser that reads one character by reference.
///
/// The parser `character(f)` reads one character `ch` from the input,
/// if `f(&ch)` is `true` then it commits and the result is `ch`,
/// otherwise it backtracks.
///
/// This does not require characters to be copyable.

pub fn character_ref<F>(f: F) -> impls::CharacterRef<F> {
    impls::CharacterRef::new(f)
}

/// A committed parser that reads one character.
///
/// The parser `CHARACTER` reads one character `ch` from the input,
/// and produces `Some(ch)`. It produces `None` at the end of input.

pub const CHARACTER: impls::AnyCharacter = impls::AnyCharacter;

/// A committed parser that reads zero characters.

pub fn emit<T>(t: T) -> impls::Emit<T> {
    impls::Emit::new(t)
}

// ----------- Tests -------------

#[allow(non_snake_case)]
impl<State, Output> ParseResult<State, Output> 
{
    pub fn unDone(self) -> Output {
        match self {
            Done(result) => result,
            _ => panic!("Not done"),
        }
    }

    pub fn unContinue(self) -> State {
        match self {
            Continue(state) => state,
            _ => panic!("Not continue"),
        }
    }

}

#[test]
fn test_character() {
    let parser = character(char::is_alphabetic);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "989".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "989");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), 'a');
    assert_eq!(data.as_str(), "bcd");
}

#[test]
fn test_character_ref() {
    fn is_alphabetic<'a>(ch: &'a char) -> bool { ch.is_alphabetic() }
    let parser = character_ref(is_alphabetic);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "989".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "989");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), 'a');
    assert_eq!(data.as_str(), "bcd");
}

#[test]
#[allow(non_snake_case)]
fn test_CHARACTER() {
    let parser = CHARACTER;
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some('a'));
    assert_eq!(data.as_str(), "bcd");
}

#[test]
fn test_map() {
    // uncommitted map
    let parser = character(char::is_alphabetic).map(Some);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "989".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "989");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some('a'));
    assert_eq!(data.as_str(), "bcd");
    // committed map
    let parser = CHARACTER.map(Some);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some(Some('a')));
    assert_eq!(data.as_str(), "bcd");
}

#[test]
fn test_discard() {
    let parser = character(char::is_alphabetic).discard();
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "989".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "989");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), ());
    assert_eq!(data.as_str(), "bcd");
}

#[test]
#[allow(non_snake_case)]
fn test_and_then() {
    // uncommitted
    let parser = character(char::is_alphabetic).and_then(CHARACTER);
    let mut data = "989".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "989");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), ('a', Some('b')));
    assert_eq!(data.as_str(), "cd");
    let mut data1 = "a".chars();
    let mut data2 = "bcd".chars();
    assert_eq!(parser.init_infer(&mut data1).unwrap().unContinue().more(&mut data2).unDone(), ('a', Some('b')));
    assert_eq!(data1.as_str(), "");
    assert_eq!(data2.as_str(), "cd");
    // committed
    let parser = CHARACTER.and_then(CHARACTER);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), (Some('a'), Some('b')));
    assert_eq!(data.as_str(), "cd");
    let mut data1 = "a".chars();
    let mut data2 = "bcd".chars();
    assert_eq!(parser.init_infer(&mut data1).unwrap().unContinue().more(&mut data2).unDone(), (Some('a'), Some('b')));
    assert_eq!(data1.as_str(), "");
    assert_eq!(data2.as_str(), "cd");
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.try_and_then(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(('a', Ok('b'))));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(('a', Err(String::from("oh")))));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_and_then_try() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.and_then_try(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok((Ok('a'), 'b')));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok((Err(String::from("oh")), 'a')));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then_try() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.try_and_then_try(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(('a', 'b')));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_and_then_discard() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.and_then_discard(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok('a'));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok('a'));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_discard_and_then() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.discard_and_then(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok('b'));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok('a'));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_and_then_try_discard() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.and_then_try_discard(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(Ok('a')));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(Err(String::from("oh"))));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_try_discard_and_then() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.try_discard_and_then(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(Ok('b')));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok(Err(String::from("oh"))));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then_try_discard() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.try_and_then_try_discard(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok('a'));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_try_discard_and_then_try() {
    fn mk_err<T>(_: Option<char>) -> Result<T, String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T, String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = ALPHANUMERIC.try_discard_and_then_try(ALPHANUMERIC);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abc".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Ok('b'));
    assert_eq!(data.as_str(), "c");
    let mut data = "a!!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "!");
    let mut data = "!ab".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Err(String::from("oh")));
    assert_eq!(data.as_str(), "b");
}

#[test]
#[allow(non_snake_case)]
fn test_or_else() {
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let NUMERIC = character(char::is_numeric).map(Some).or_else(CHARACTER.map(mk_none));
    let ALPHABETIC = character(char::is_alphabetic).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = character(char::is_alphabetic).and_then(ALPHABETIC).map(Some)
                     .or_else(character(char::is_numeric).and_then(NUMERIC).map(Some))
                     .or_else(CHARACTER.map(mk_none));
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "abcd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some(('a', Some('b'))));
    assert_eq!(data.as_str(), "cd");
    let mut data = "a89".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some(('a', None)));
    assert_eq!(data.as_str(), "9");
    let mut data = "789".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some(('7', Some('8'))));
    assert_eq!(data.as_str(), "9");
    let mut data = "7cd".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), Some(('7', None)));
    assert_eq!(data.as_str(), "d");
    let mut data = "!?".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), None);
    assert_eq!(data.as_str(), "?");
}

#[test]
#[allow(non_snake_case)]
fn test_plus() {
    let parser = character(char::is_alphanumeric).plus(String::new);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "!?".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "!?");
    let mut data = "abc!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), "abc");
    assert_eq!(data.as_str(), "!");
    let mut data1 = "ab".chars();
    let mut data2 = "c!".chars();
    assert_eq!(parser.init_infer(&mut data1).unwrap().unContinue().more(&mut data2).unDone(), "abc");
    assert_eq!(data.as_str(), "!");
}

#[test]
#[allow(non_snake_case)]
fn test_star() {
    let parser = character(char::is_alphanumeric).star(String::new);
    let mut data = "".chars();
    assert!(parser.init_infer(&mut data).is_none());
    assert_eq!(data.as_str(), "");
    let mut data = "!?".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), "");
    assert_eq!(data.as_str(), "!?");
    let mut data = "abc!".chars();
    assert_eq!(parser.init_infer(&mut data).unwrap().unDone(), "abc");
    assert_eq!(data.as_str(), "!");
    let mut data1 = "ab".chars();
    let mut data2 = "c!".chars();
    assert_eq!(parser.init_infer(&mut data1).unwrap().unContinue().more(&mut data2).unDone(), "abc");
    assert_eq!(data.as_str(), "!");
}

// #[test]
// #[allow(non_snake_case)]
// fn test_buffer() {
//     use std::borrow::Cow::{Borrowed,Owned};
//     fn ignore() {}
//     let ALPHABETIC = character(char::is_alphabetic);
//     let ALPHANUMERIC = character(char::is_alphanumeric);
//     let parser = ALPHABETIC.and_then(ALPHANUMERIC.star(ignore)).buffer();
//     let mut data = "".chars();
//     assert!(parser.init_infer(&mut data).is_none());
//     assert_eq!(data.as_str(), "");
//     let mut data = "!?".chars();
//     assert!(parser.init_infer(&mut data).is_none());
//     assert_eq!(data.as_str(), "!?");
//     let mut data = "abc!".chars();
//     if let Borrowed(result) = parser.init_infer(&mut data).unwrap().unDone() {
//         assert_eq!(result, "abc");
//     } else { panic!("cow") }
//     assert_eq!(data.as_str(), "!");
//     let mut data1 = "abc".chars();
//     let mut data2 = "def!".chars();
//     if let Owned(result) = parser.init_infer(&mut data1).unwrap().unContinue().more(&mut data2).unDone() {
//         assert_eq!(result, "abcdef");
//     } else { panic!("cow") }
//     assert_eq!(data.as_str(), "!");
// }

// #[test]
// #[allow(non_snake_case)]
// fn test_cow() {
//     fn is_foo<'a>(string: &Cow<'a,str>) -> bool { string == "foo" }
//     fn mk_other<'a>(_: Option<Cow<'a,str>>) -> Cow<'a,str> { Cow::Borrowed("other") }
//     fn is_owned<'a,T:?Sized+ToOwned>(cow: Cow<'a,T>) -> bool { match cow { Cow::Owned(_) => true, _ => false } }
//     let ONE = character_ref(is_foo);
//     let OTHER = CHARACTER.map(mk_other);
//     let parser = ONE.and_then(ONE.or_else(OTHER)).and_then(ONE.or_else(OTHER));
//     let mut data = vec![Cow::Borrowed("foo"), Cow::Borrowed("bar"), Cow::Borrowed("foo")];
//     let ((fst, snd), thd) = parser.init_infer(&mut data.drain(..).peekable()).unwrap().unDone();
//     assert_eq!(fst, "foo");
//     assert_eq!(snd, "other");
//     assert_eq!(thd, "foo");
//     assert!(!is_owned(fst));
//     assert!(!is_owned(snd));
//     assert!(!is_owned(thd));
//     let mut data1 = vec![Cow::Borrowed("foo")];
//     let mut data2 = vec![Cow::Borrowed("bar"), Cow::Borrowed("foo")];
//     let ((fst, snd), thd) = parser.init_infer(&mut data1.drain(..).peekable()).unwrap().unContinue()
//         .more(&mut data2.drain(..).peekable()).unDone();
//     assert_eq!(fst, "foo");
//     assert_eq!(snd, "other");
//     assert_eq!(thd, "foo");
//     assert!(is_owned(fst));
//     assert!(!is_owned(snd));
//     assert!(!is_owned(thd));
//     let mut data1 = vec![Cow::Borrowed("foo"), Cow::Borrowed("bar")];
//     let mut data2 = vec![Cow::Borrowed("foo")];
//     let ((fst, snd), thd) = parser.init_infer(&mut data1.drain(..).peekable()).unwrap().unContinue()
//         .more(&mut data2.drain(..).peekable()).unDone();
//     assert_eq!(fst, "foo");
//     assert_eq!(snd, "other");
//     assert_eq!(thd, "foo");
//     assert!(is_owned(fst));
//     assert!(is_owned(snd));
//     assert!(!is_owned(thd));
// }

// #[test]
// #[allow(non_snake_case)]
// fn test_boxable() {
//     use std::vec::Drain;
//     #[derive(Copy, Clone, Debug)]
//     struct Test;
//     type TestCh<'a> = Cow<'a,str>;
//     type TestInput<'a> = Peekable<Drain<'a,TestCh<'a>>>;
//     type TestOutput<'a> = ((TestCh<'a>, TestCh<'a>), TestCh<'a>);
//     type TestState = Box<for<'a> Boxable<TestInput<'a>, TestOutput<'a>>>;
//     fn mk_box<P>(parser: P) -> TestState
//         where P: 'static + for<'a> Boxable<TestInput<'a>, TestOutput<'a>>
//     { Box::new(parser) }
//     impl Parser for Test {}
//     impl<'a> Infer<TestInput<'a>> for Test {
//         type Output = TestOutput<'a>;
//         type State = TestState;
//     }
//     impl<'a> Uncommitted<TestState, TestInput<'a>, TestOutput<'a>> for Test {
//         fn init(&self, data: &mut TestInput<'a>) -> Option<ParseResult<TestState, TestOutput<'a>>> {
//             fn is_foo<'a>(string: &Cow<'a,str>) -> bool { string == "foo" }
//             fn mk_other<'a>(_: Option<TestCh<'a>>) -> TestCh<'a> { Cow::Borrowed("other") }
//             let ONE = character_ref(is_foo);
//             let OTHER = CHARACTER.map(mk_other);
//             let parser = ONE.and_then(ONE.or_else(OTHER)).and_then(ONE.or_else(OTHER));
//             parser.boxed(mk_box).init(data)
//         }
//     }
//     fn is_owned<'a,T:?Sized+ToOwned>(cow: Cow<'a,T>) -> bool { match cow { Cow::Owned(_) => true, _ => false } }
//     let parser = Test; 
//     let mut data = vec![Cow::Borrowed("foo"), Cow::Borrowed("bar"), Cow::Borrowed("foo")];
//     let ((fst, snd), thd) = parser.init_infer(&mut data.drain(..).peekable()).unwrap().unDone();
//     assert_eq!(fst, "foo");
//     assert_eq!(snd, "other");
//     assert_eq!(thd, "foo");
//     assert!(!is_owned(fst));
//     assert!(!is_owned(snd));
//     assert!(!is_owned(thd));
//     let mut data1 = vec![Cow::Borrowed("foo")];
//     let mut data2 = vec![Cow::Borrowed("bar"), Cow::Borrowed("foo")];
//     let ((fst, snd), thd) = parser.init_infer(&mut data1.drain(..).peekable()).unwrap().unContinue()
//         .more(&mut data2.drain(..).peekable()).unDone();
//     assert_eq!(fst, "foo");
//     assert_eq!(snd, "other");
//     assert_eq!(thd, "foo");
//     assert!(is_owned(fst));
//     assert!(!is_owned(snd));
//     assert!(!is_owned(thd));
//     let mut data1 = vec![Cow::Borrowed("foo"), Cow::Borrowed("bar")];
//     let mut data2 = vec![Cow::Borrowed("foo")];
//     let ((fst, snd), thd) = parser.init_infer(&mut data1.drain(..).peekable()).unwrap().unContinue()
//         .more(&mut data2.drain(..).peekable()).unDone();
//     assert_eq!(fst, "foo");
//     assert_eq!(snd, "other");
//     assert_eq!(thd, "foo");
//     assert!(is_owned(fst));
//     assert!(is_owned(snd));
//     assert!(!is_owned(thd));
// }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_iter() {
// //     fn mk_X(_: Option<char>) -> char {
// //         'X'
// //     }
// //     let ALPHABETIC = character(char::is_alphabetic);
// //     let parser = ALPHABETIC.or_else(CHARACTER.map(mk_X));
// //     let mut iter = parser.iter("abc");
// //     assert_eq!(iter.next(), Some('a'));
// //     assert_eq!(iter.next(), Some('b'));
// //     assert_eq!(iter.next(), Some('c'));
// //     assert_eq!(iter.next(), None);
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_pipe() {
// //     use std::borrow::{Borrow, Cow};
// //     #[derive(Clone,Debug,PartialEq,Eq)]
// //     enum Token {
// //         Identifier(String),
// //         Number(usize),
// //         Other,
// //     }
// //     fn mk_id<'a>(string: Cow<'a, str>) -> Token {
// //         Token::Identifier(string.into_owned())
// //     }
// //     fn mk_num<'a>(string: Cow<'a, str>) -> Token {
// //         Token::Number(usize::from_str_radix(string.borrow(), 10).unwrap())
// //     }
// //     fn mk_other(_: Option<char>) -> Token {
// //         Token::Other
// //     }
// //     fn ignore() {}
// //     fn is_decimal(ch: char) -> bool {
// //         ch.is_digit(10)
// //     }
// //     fn is_identifier(tok: &Token) -> bool {
// //         match *tok {
// //             Token::Identifier(_) => true,
// //             _ => false,
// //         }
// //     }
// //     fn is_number(tok: &Token) -> bool {
// //         match *tok {
// //             Token::Number(_) => true,
// //             _ => false,
// //         }
// //     }
// //     let ALPHABETIC = character(char::is_alphabetic);
// //     let DIGIT = character(is_decimal);
// //     let lexer = ALPHABETIC.plus(ignore)
// //                           .buffer()
// //                           .map(mk_id)
// //                           .or_else(DIGIT.plus(ignore).buffer().map(mk_num))
// //                           .or_else(CHARACTER.map(mk_other));
// //     let parser = token(is_identifier).or_else(token(is_number)).star(Vec::<Token>::new);
// //     assert_eq!(lexer.pipe(parser).init_infer().parse("abc37!!").unDone(),
// //                ("!",
// //                 vec![Token::Identifier(String::from("abc")), Token::Number(37)]));
// // }
