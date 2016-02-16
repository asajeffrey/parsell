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
//! [Repo](https://github.com/asajeffrey/parsell) |
//! [Crate](https://crates.io/crates/parsell) |
//! [CI](https://travis-ci.org/asajeffrey/parsell)

#![feature(unboxed_closures)]

use self::MaybeParseResult::{Backtrack, Commit};
use self::ParseResult::{Done, Continue};

// use std::fmt::{Formatter, Debug};
use std::borrow::Cow;
// use std::str::Chars;

pub mod impls;

// ----------- Types for parsers ------------

/// A trait for stateful parsers.
///
/// Stateful parsers are typically constructed by calling the `init` method of a stateless parser,
/// for example:
///
/// ```text
/// # use parsell::{character,Parser,Uncommitted,Committed};
/// let stateless = character(char::is_alphanumeric).star(String::new);
/// let stateful = stateless.init();
/// ```
///
/// Here, `stateless` is a `Committed<&str,Output=String>`, and `stateful` is a `Stateful<&str,Output=String>`.
///
/// The reason for distinguishing between stateful and stateless parsers is that
/// stateless parsers are usually copyable, whereas stateful parsers are usually not
/// (they may, for example, have created and partially filled some buffers).
/// Copying parsers is quite common, for example:
///
/// ```text
/// # use parsell::{character,CHARACTER,Uncommitted,Parser,Committed,Stateful};
/// # use parsell::ParseResult::Done;
/// fn mk_err(_: Option<char>) -> Result<char,String> { Err(String::from("Expecting a digit")) }
/// let DIGIT = character(char::is_numeric).map(Ok).or_else(CHARACTER.map(mk_err));
/// let TWO_DIGITS = DIGIT.try_and_then_try(DIGIT);
/// match TWO_DIGITS.init().parse("123") {
///    Done("3",result) => assert_eq!(result,Ok(('1','2'))),
///    _ => panic!("Can't happen"),
/// }
/// ```

pub trait Stateful<Ch, Str> 
    where Str: Iterator<Item = Ch>,
{
    
    /// The type of the data being produced by the parser.
    type Output;

    /// Parse a non-empty string of data.
    fn more(self, ch: Ch, string: Str) -> ParseResult<Ch, Str, Self, Self::Output>
        where Self: Sized;

    /// Parse an EOF.
    fn done(self) -> Self::Output
        where Self: Sized;

}

// //     /// Provides data to the parser.
// //     ///
// //     /// If `parser: Stateful<S,Output=T>`, then `parser.parse(data)` either:
// //     ///
// //     /// * returns `Done(rest, result)` where `rest: S` is any remaining input,
// //     ///   and `result: T` is the parsed output, or
// //     /// * returns `Continue(rest,parsing)` where `parsing: Self` is the new state of the parser.
// //     ///
// //     /// For example:
// //     ///
// //     /// ```
// //     /// # use parsell::{character,Parser,Uncommitted,Committed,Stateful};
// //     /// # use parsell::ParseResult::{Continue,Done};
// //     /// let parser = character(char::is_alphabetic).star(String::new);
// //     /// let stateful = parser.init();
// //     /// match stateful.parse("abc") {
// //     ///     Continue("",parsing) => match parsing.parse("def!") {
// //     ///         Done("!",result) => assert_eq!(result,"abcdef"),
// //     ///         _ => panic!("can't happen"),
// //     ///     },
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// ```
// //     ///
// //     /// Note that `parser.parse(data)` consumes both the `parser` and the `data`. In particular,
// //     /// the `parser` is no longer available, so the following does not typecheck:
// //     ///
// //     /// ```text
// //     /// let parser = character(char::is_alphabetic).star(String::new);
// //     /// let stateful = parser.init();
// //     /// stateful.parse("abc");
// //     /// stateful.parse("def!");
// //     /// ```
// //     ///
// //     /// This helps with parser safety, as it stops a client from calling `parse` after a
// //     /// a stateful parser has finished.
// //     fn parse(self, value: Str) -> ParseResult<Self, Str> where Self: Sized;

// //     /// Tells the parser that it will not receive any more data.
// //     ///
// //     /// If `parser: Stateful<S,Output=T>`, then `parser.done()` returns a result of type `T`
// //     /// for example:
// //     ///
// //     /// ```
// //     /// # use parsell::{character,Parser,Uncommitted,Committed,Stateful};
// //     /// # use parsell::ParseResult::{Continue,Done};
// //     /// let parser = character(char::is_alphabetic).star(String::new);
// //     /// let stateful = parser.init();
// //     /// match stateful.parse("abc") {
// //     ///     Continue("",parsing) => match parsing.parse("def") {
// //     ///         Continue("",parsing) => assert_eq!(parsing.done(),"abcdef"),
// //     ///         _ => panic!("can't happen"),
// //     ///     },
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// ```
// //     ///
// //     /// Note that `parser.done()` consumes the `parser`. In particular,
// //     /// the `parser` is no longer available, so the following does not typecheck:
// //     ///
// //     /// ```text
// //     /// let parser = character(char::is_alphabetic).star(String::new);
// //     /// let stateful = parser.init();
// //     /// stateful.done();
// //     /// stateful.parse("def!");
// //     /// ```
// //     ///
// //     /// This helps with parser safety, as it stops a client from calling `parse` after a
// //     /// a stateful parser has finished.
// //     fn done(self) -> Self::Output where Self: Sized;

// //     /// Make this parser boxable.
// //     fn boxable(self) -> impls::BoxableParser<Self>
// //         where Self: Sized
// //     {
// //         impls::BoxableParser::new(self)
// //     }

// // }

/// The result of stateful parsing
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ParseResult<Ch, Str, Continuation, Output> {
    
    /// The parse is finished.
    Done(Ch, Str, Output),
    
    /// The parse can continue.
    Continue(Str, Continuation),

}

/// A trait for stateless parsers.
///
/// Parsers are implemented either as committed parsers, which cannot backtrack,
/// or uncommitted parsers, which can backtrack on their first token of input.
/// For example `character(char::is_alphabetic)` is uncommitted because
/// it will backtrack on any non-alphabetic character, but
/// `CHARACTER` is not, because it will produce `None` rather than backtracking.

pub trait Committed<Ch, Str>
    where Str: Iterator<Item = Ch>,
{

    type Output;
    type State: 'static + Stateful<Ch, Str, Output=Self::Output>;

    /// Parse a non-empty string of data.
    fn init(&self, ch: Ch, string: Str) -> ParseResult<Ch, Str, Self::State, Self::Output>;

    /// Parse an empty string of data.
    fn empty(&self) -> Self::Output;

}

// pub enum Impossible {}

// impl Impossible {
//     fn cant_happen<T>(&self) -> T { match *self {} }
// }

pub trait Uncommitted<Ch, Str>
    where Str: Iterator<Item = Ch>,
{

    type Output;
    type State: 'static + Stateful<Ch, Str, Output=Self::Output>;

    /// Parse a non-empty string of data.
    fn init_maybe(&self, ch: Ch, string: Str) -> MaybeParseResult<Ch, Str, Self::State, Self::Output>;

}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum MaybeParseResult<Ch, Str, Resumption, Output> {
    Backtrack(Ch, Str),
    Commit(ParseResult<Ch, Str, Resumption, Output>),
}

pub trait Parser {

//     /// Choice between parsers
//     fn or_else<P>(self, other: P) -> impls::OrElse<Self, P>
//         where Self: Sized,
//               P: Parser,
//     {
//         impls::OrElse::new(self, other)
//     }

    /// Sequencing with a committed parser
    fn and_then<P>(self, other: P) -> impls::AndThen<Self, P>
        where Self: Sized,
              P: Parser,
    {
        impls::AndThen::new(self, other)
    }

// //     /// Sequencing with a committed parser (bubble any errors from this parser).
// //     fn try_and_then<P>(self,
// //                        other: P)
// //                        -> impls::MapParser<impls::AndThenParser<Self, P>, impls::TryZip>
// //         where Self: Sized,
// //               P: Parser<Ch>,
// //     {
// //         self.and_then(other).map(impls::TryZip)
// //     }

// //     /// Sequencing with a committed parser (bubble any errors from that parser).
// //     fn and_then_try<P>(self,
// //                        other: P)
// //                        -> impls::MapParser<impls::AndThenParser<Self, P>, impls::ZipTry>
// //         where Self: Sized,
// //               P: Parser<Ch>,

// //     {
// //         self.and_then(other).map(impls::ZipTry)
// //     }

// //     /// Sequencing with a committed parser (bubble any errors from either parser).
// //     fn try_and_then_try<P>(self,
// //                            other: P)
// //                            -> impls::MapParser<impls::AndThenParser<Self, P>, impls::TryZipTry>
// //         where Self: Sized,
// //               P: Parser<Ch>,
// //     {
// //         self.and_then(other).map(impls::TryZipTry)
// //     }

// //     /// Iterate one or more times (returns an uncommitted parser).
// //     fn plus<F>(self, factory: F) -> impls::PlusParser<Self, F>
// //         where Self: Sized,
// //               F: Factory,
// //     {
// //         impls::PlusParser::new(self, factory)
// //     }

// //     /// Iterate zero or more times (returns a committed parser).
// //     fn star<F>(self, factory: F) -> impls::StarParser<Self, F>
// //         where Self: Sized,
// //               F: Factory,
// //     {
// //         impls::StarParser::new(self, factory)
// //     }

    /// Apply a function to the result
    fn map<F>(self, f: F) -> impls::Map<Self, F>
        where Self: Sized,
    {
        impls::Map::new(self, f)
    }

// //     /// Apply a 2-arguent function to the result
// //     fn map2<F>(self, f: F) -> impls::MapParser<Self, impls::Function2<F>>
// //         where Self: Sized,
// //     {
// //         impls::MapParser::new(self, impls::Function2::new(f))
// //     }

// //     /// Apply a 3-arguent function to the result
// //     fn map3<F>(self, f: F) -> impls::MapParser<Self, impls::Function3<F>>
// //         where Self: Sized,
// //     {
// //         impls::MapParser::new(self, impls::Function3::new(f))
// //     }

// //     /// Apply a 4-arguent function to the result
// //     fn map4<F>(self, f: F) -> impls::MapParser<Self, impls::Function4<F>>
// //         where Self: Sized,
// //     {
// //         impls::MapParser::new(self, impls::Function4::new(f))
// //     }

// //     /// Apply a 5-arguent function to the result
// //     fn map5<F>(self, f: F) -> impls::MapParser<Self, impls::Function5<F>>
// //         where Self: Sized,
// //     {
// //         impls::MapParser::new(self, impls::Function5::new(f))
// //     }

// //     /// Apply a function to the result (bubble any errors).
// //     fn try_map<F>(self, f: F) -> impls::MapParser<Self, impls::Try<F>>
// //         where Self: Sized
// //     {
// //         self.map(impls::Try::new(f))
// //     }

// //     /// Apply a 2-argument function to the result (bubble any errors).
// //     fn try_map2<F>(self, f: F) -> impls::MapParser<Self, impls::Try<impls::Function2<F>>>
// //         where Self: Sized
// //     {
// //         self.try_map(impls::Function2::new(f))
// //     }

// //     /// Apply a 3-argument function to the result (bubble any errors).
// //     fn try_map3<F>(self, f: F) -> impls::MapParser<Self, impls::Try<impls::Function3<F>>>
// //         where Self: Sized
// //     {
// //         self.try_map(impls::Function3::new(f))
// //     }

// //     /// Apply a 4-argument function to the result (bubble any errors).
// //     fn try_map4<F>(self, f: F) -> impls::MapParser<Self, impls::Try<impls::Function4<F>>>
// //         where Self: Sized
// //     {
// //         self.try_map(impls::Function4::new(f))
// //     }

// //     /// Apply a 5-argument function to the result (bubble any errors).
// //     fn try_map5<F>(self, f: F) -> impls::MapParser<Self, impls::Try<impls::Function5<F>>>
// //         where Self: Sized
// //     {
// //         self.try_map(impls::Function5::new(f))
// //     }

// //     /// Take the results of iterating this parser, and feed it into another parser.
// //     // fn pipe<P>(self, other: P) -> impls::PipeParser<Self, P>
// //     //     where Self: Sized
// //     // {
// //     //     impls::PipeParser::new(self, other)
// //     // }

// //     /// A parser which produces its input.
// //     ///
// //     /// This does its best to avoid having to buffer the input. The result of a buffered parser
// //     /// may be borrowed (because no buffering was required) or owned (because buffering was required).
// //     /// Buffering is required in the case that the input was provided in chunks, rather than
// //     /// contiguously. For example:
// //     ///
// //     /// ```
// //     /// # use parsell::{character,Parser,Uncommitted,Stateful};
// //     /// # use parsell::MaybeParseResult::{Commit};
// //     /// # use parsell::ParseResult::{Done,Continue};
// //     /// # use std::borrow::Cow::{Borrowed,Owned};
// //     /// fn ignore() {}
// //     /// let parser = character(char::is_alphabetic).plus(ignore).buffer();
// //     /// match parser.parse("abc!") {
// //     ///     Commit(Done("!",Borrowed(result))) => assert_eq!(result,"abc"),
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// match parser.parse("abc") {
// //     ///     Commit(Continue("",parsing)) => match parsing.parse("def!") {
// //     ///         Done("!",Owned(result)) => assert_eq!(result,"abcdef"),
// //     ///         _ => panic!("can't happen"),
// //     ///     },
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// ```
// //     fn buffer(self) -> impls::BufferedParser<Self>
// //         where Self: Sized
// //     {
// //         impls::BufferedParser::new(self)
// //     }

    fn init_iter<Ch, Str, State, Output>(&self, mut string: Str) -> Option<ParseResult<Ch, Str, State, Output>>
        where Self: Committed<Ch, Str, State = State, Output = Output>,
              State: 'static + Stateful<Ch, Str, Output = Output>,
              Str: Iterator<Item = Ch>,
    {
        string.next().map(|ch| self.init(ch, string))
    }
    
    fn init_iter_maybe<Ch, Str, State, Output>(&self, mut string: Str) -> Option<MaybeParseResult<Ch, Str, State, Output>>
        where Self: Uncommitted<Ch, Str, State = State, Output = Output>,
              State: 'static + Stateful<Ch, Str, Output = Output>,
              Str: Iterator<Item = Ch>,
    {
        string.next().map(|ch| self.init_maybe(ch, string))
    }
    
}

// // /// A trait for committed parsers.
// // ///
// // /// A parser is committed if it is guaranteed not to backtrack.
// // /// Committed parsers are typically constructed by calling the methods of the library,
// // /// for example:
// // ///
// // /// ```
// // /// # use parsell::{character,Parser,Uncommitted};
// // /// let parser = character(char::is_alphanumeric).star(String::new);
// // /// ```
// // ///
// // /// Here, `parser` is a `Committed<&str,Output=String>`.
// // ///
// // /// The reason for distinguishing between committed and uncommitted parsers
// // /// is that the library is designed for LL(1) grammars, that only use one token
// // /// of lookahead. This means that the sequence of two parsers
// // /// `p.and_then(q)` is only well-defined when `q` is committed,
// // /// since if `p` commits, then `q` cannot backtrack.
// // ///
// // /// Semantically, a parser with input *S* and output *T* is a partial function *S\* → T*
// // /// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain)
// // /// and non-empty.

// // pub trait Committed<Str>: Parser<<Str::Item as ToStatic>::Static>
// //     where Str: IntoPeekable,
// //           Str::Item: ToStatic,
// // {

// //     /// Create a stateful parser by initializing a stateless parser.
// //     fn init(&self) -> Self::State;

// //     /// Build an iterator from a parser and some data.
// //     fn iter(self, data: Str) -> impls::IterParser<Self, Self::State, Str>
// //         where Self: Sized + Copy
// //     {
// //         impls::IterParser::new(self, data)
// //     }

// //     /// Short hand for calling init then parse.
// //     fn init_parse(&self, data: Str) -> ParseResult<Self::State, Str>
// //         where Self: Sized,
// //               Self::State: Stateful<Str>,
// //     {
// //         self.init().parse(data)
// //     }

// // }

// // /// A trait for uncommitted parsers.
// // ///
// // /// An uncommitted parser can decide based on the first token of input whether
// // /// it will commit to parsing, or immediately backtrack and try another option.
// // ///
// // /// The advantage of uncommitted parsers over committed parsers is they support choice:
// // /// `p.or_else(q)` will try `p`, and commit if it commits, but if it backtracks
// // /// will then try `q`. For example:
// // ///
// // /// ```
// // /// # use parsell::{character,CHARACTER,Parser,Uncommitted,Committed,Stateful};
// // /// # use parsell::ParseResult::Done;
// // /// fn default(_: Option<char>) -> String { String::from("?") }
// // /// let parser =
// // ///    character(char::is_numeric).plus(String::new)
// // ///        .or_else(character(char::is_alphabetic).plus(String::new))
// // ///        .or_else(CHARACTER.map(default));
// // /// match parser.init().parse("123abc") {
// // ///    Done("abc",result) => assert_eq!(result,"123"),
// // ///    _ => panic!("Can't happen"),
// // /// }
// // /// match parser.init().parse("abc123") {
// // ///    Done("123",result) => assert_eq!(result,"abc"),
// // ///    _ => panic!("Can't happen"),
// // /// }
// // /// match parser.init().parse("!@#") {
// // ///    Done("@#",result) => assert_eq!(result,"?"),
// // ///    _ => panic!("Can't happen"),
// // /// }
// // /// ```
// // ///
// // /// Semantically, a parser with input *S* and output *T* is a partial function *S\+ → T*
// /// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain).

// // pub trait Uncommitted<Str>: Parser<<Str::Item as ToStatic>::Static>
// //     where Str: IntoPeekable,
// //           Str::Item: ToStatic,
// // {

// //     /// Provides data to the parser.
// //     ///
// //     /// If `parser: Uncommitted<S,Output=T>`, then `parser.parse(data)` either:
// //     ///
// //     /// * returns `Empty(data)` because `data` was empty,
// //     /// * returns `Abort(data)` because the parser should backtrack, or
// //     /// * returns `Commit(result)` because the parser has committed.
// //     ///
// //     /// For example:
// //     ///
// //     /// ```
// //     /// # use parsell::{character,Parser,Uncommitted,Stateful};
// //     /// # use parsell::MaybeParseResult::{Empty,Commit,Abort};
// //     /// # use parsell::ParseResult::{Done,Continue};
// //     /// let parser = character(char::is_alphabetic).plus(String::new);
// //     /// match parser.parse("") {
// //     ///     Empty("") => (),
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// match parser.parse("!abc") {
// //     ///     Abort("!abc") => (),
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// match parser.parse("abc!") {
// //     ///     Commit(Done("!",result)) => assert_eq!(result,"abc"),
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// match parser.parse("abc") {
// //     ///     Commit(Continue("",parsing)) => match parsing.parse("def!") {
// //     ///         Done("!",result) => assert_eq!(result,"abcdef"),
// //     ///         _ => panic!("can't happen"),
// //     ///     },
// //     ///     _ => panic!("can't happen"),
// //     /// }
// //     /// ```
// //     ///
// //     /// Note that the decision to commit or abort must be made on the first
// //     /// token of data (since the parser only retries on empty input)
// //     /// so this is appropriate for LL(1) grammars that only perform one token
// //     /// of lookahead.
// //     fn parse(&self, value: Str) -> MaybeParseResult<Self::State, Str>
// //         where Self: Sized,
// //               Self::State: Stateful<Str>;

// // }

// // /// The result of a parse.
// // pub enum MaybeParseResult<P, S>
// //     where P: Stateful<S>
// // {
// //     /// The input was empty.
// //     Empty(S),
// //     /// The parser must backtrack.
// //     Abort(S),
// //     /// The parser has committed to parsing the input.
// //     Commit(ParseResult<P, S>),
// // }

// // impl<P, S> MaybeParseResult<P, S> where P: Stateful<S>
// // {
// //     /// Apply a function the the Commit branch of a parse result
// //     pub fn map<F, Q>(self, f: F) -> MaybeParseResult<Q, S>
// //         where Q: Stateful<S, Output = P::Output>,
// //               F: Function<P, Output = Q>
// //     {
// //         match self {
// //             Empty(rest) => Empty(rest),
// //             Abort(s) => Abort(s),
// //             Commit(c) => Commit(c.map(f)),
// //         }
// //     }
// // }

// // // Implement Debug for MaybeParseResult<P, S> without requiring P: Debug

// // impl<P, S> Debug for MaybeParseResult<P, S>
// //     where P: Stateful<S>,
// //           S: Debug,
// //           P::Output: Debug,
// // {
// //     fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
// //         match self {
// //             &Empty(ref rest) => write!(fmt, "Empty({:?})", rest),
// //             &Abort(ref rest) => write!(fmt, "Abort({:?})", rest),
// //             &Commit(ref result) => write!(fmt, "Commit({:?})", result),
// //         }
// //     }
// // }

// // impl<P,S> PartialEq for MaybeParseResult<P, S> where S: PartialEq, P: Stateful<S>, P::Output: PartialEq {
// //     fn eq(&self, other: &MaybeParseResult<P, S>) -> bool {
// //         match (self, other) {
// //             (&Empty(ref rest1), &Empty(ref rest2)) => (rest1 == rest2),
// //             (&Abort(ref rest1), &Abort(ref rest2)) => (rest1 == rest2),
// //             (&Commit(ref result1), &Commit(ref result2)) => (result1 == result2),
// //             _ => false,
// //         }
// //     }
// // }

// // /// A trait for boxable parsers.
// // ///
// // /// Regular languages can be parsed in constant memory, so do not require any heap allocation (other than
// // /// the heap allocation peformed by user code such as creating buffers). Context-free languages require
// // /// allocating unbounded memory. In order to support streaming input, the state of the parser must be
// // /// saved on the heap, and restored when more input arrives.
// // ///
// // /// In Rust, heap-allocated data is often kept in a `Box<T>`, where `T` is a trait. In the case
// // /// of parsers, the library needs to save and restore a stateful parser, for which the obvious
// // /// type is `Box<Stateful<S,Output=T>`. There are two issues with this...
// // ///
// // /// Firstly, the lifetimes mentioned in the type of the parser may change over time.
// // /// For example, the program:
// // ///
// // /// ```text
// // /// fn check_results (self, rest: &'b str, result: String) {
// // ///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
// // /// }
// // /// let parser = character(char::is_alphanumeric).star(String::new);
// // /// let stateful = parser.init();
// // /// let boxed: Box<Stateful<&'a str,Output=String>> = Box::new(stateful);
// // /// let stuff: &'b str = "abc123!";
// // /// match boxed.parse(stuff) {
// // ///    Done(rest,result) => self.check_results(rest,result),
// // ///    _ => println!("can't happen"),
// // /// }
// // /// ```
// // ///
// // /// does not typecheck, because the type of `boxed` is fixed as containing parsers for input `&'a str`,
// // /// but it was fed input of type `&'b str`. To fix this, we change the type of the box to be
// // /// polymorphic in the lifetime of the parser:
// // ///
// // /// ```text
// // /// fn check_results (self, rest: &'b str, result: String) {
// // ///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
// // /// }
// // /// let parser = character(char::is_alphanumeric).star(String::new);
// // /// let stateful = parser.init();
// // /// let boxed: Box<for <'a> Stateful<&'a str,Output=String>> = Box::new(stateful);
// // /// let stuff: &'b str = "abc123!";
// // /// match boxed.parse(stuff) {
// // ///    Done(rest,result) => self.check_results(rest,result),
// // ///    _ => println!("can't happen"),
// // /// }
// // /// ```
// // ///
// // /// Secondly, the `Stateful` trait is not
// // /// [object-safe](https://doc.rust-lang.org/book/trait-objects.html#object-safety),
// // /// so cannot be boxed and unboxed safely. In order to address this, there is a trait
// // /// `Boxable<S,Output=T>`, which represents stateful parsers, but is object-safe
// // /// and so can be boxed and unboxed safely:
// // ///
// // /// ```
// // /// # struct Foo<'a>(&'a str);
// // /// # impl<'b> Foo<'b> {
// // /// fn check_results (self, rest: &'b str, result: String) {
// // ///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
// // /// }
// // /// # fn foo(self) {
// // /// # use parsell::{character,Parser,Uncommitted,Committed,Boxable,Stateful};
// // /// # use parsell::ParseResult::{Done,Continue};
// // /// let parser = character(char::is_alphanumeric).star(String::new);
// // /// let stateful = parser.init();
// // /// let boxed: Box<for <'a> Boxable<&'a str,Output=String>> = Box::new(stateful.boxable());
// // /// let stuff: &'b str = "abc123!";
// // /// match boxed.parse(stuff) {
// // ///    Done(rest,result) => self.check_results(rest,result),
// // ///    _ => println!("can't happen"),
// // /// }
// // /// # } }
// // /// ```
// // ///
// // /// The type `Box<Boxable<S,Output=T>>` implements the trait
// // /// `Stateful<S,Output=T>`, so boxes can be used as parsers,
// // /// which allows stateful parsers to heap-allocate their state.
// // ///
// // /// Boxable parsers are usually used in recursive-descent parsing,
// // /// for context-free grammars that cannot be parsed as a regular language.
// // /// For example, consider a simple type for trees:
// // ///
// // /// ```
// // /// # use parsell::{Static};
// // /// struct Tree(Vec<Tree>);
// // /// impl Static for Tree {}
// // /// ```
// // ///
// // /// which can be parsed from a well-nested sequence of parentheses, for example
// // /// `(()())` can be parsed as `Tree(vec![Tree(vec![]),Tree(vec![])])`.
// // /// The desired implementation is:
// // ///
// // /// ```text
// // /// fn is_lparen(ch: char) -> bool { ch == '(' }
// // /// fn is_rparen(ch: char) -> bool { ch == ')' }
// // /// fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
// // /// fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
// // /// fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
// // /// fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Tree {
// // ///     Tree(children)
// // /// }
// // /// let LPAREN = character(is_lparen);
// // /// let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
// // /// let TREE = LPAREN
// // ///     .and_then_try(TREE.star(mk_vec))
// // ///     .try_and_then_try(RPAREN)
// // ///     .try_map3(mk_tree);
// // /// ```
// // ///
// // /// but this doesn't work because it gives the definition of `TREE` in terms of itself,
// // /// and Rust doesn't allow this kind of cycle.
// // ///
// // /// Instead, the solution is to define a struct `TreeParser`, and then implement `Uncommitted<&str>`
// // /// for it. The type of the state of a `TreeParser` is a box containing an appropriate
// // /// `BoxableParserState` trait:
// // ///
// // /// ```
// // /// # use parsell::{Boxable, Static};
// // /// # struct Tree(Vec<Tree>);
// // /// # impl Static for Tree {}
// // /// type TreeParserState = Box<for<'b> Boxable<&'b str, Output=Tree>>;
// // /// ```
// // ///
// // /// The implementation of `Uncommitted<&str>` for `TreeParser` is mostly straightfoward:
// // ///
// // /// ```
// // /// # use parsell::{character,CHARACTER,Parser,Uncommitted,Committed,Boxable,Stateful,MaybeParseResult,Static};
// // /// # use parsell::ParseResult::{Done,Continue};
// // /// # use parsell::MaybeParseResult::{Commit};
// // /// # #[derive(Eq,PartialEq,Clone,Debug)]
// // /// struct Tree(Vec<Tree>);
// // /// impl Static for Tree {}
// // /// # #[derive(Copy,Clone,Debug)]
// // /// struct TreeParser;
// // /// type TreeParserState = Box<for<'b> Boxable<&'b str, Output=Result<Tree,String>>>;
// // /// impl Parser<char> for TreeParser {
// // ///     type StaticOutput = Result<Tree,String>;
// // ///     type State = TreeParserState;
// // /// }
// // /// impl<'a> Uncommitted<&'a str> for TreeParser {
// // ///     fn parse(&self, data: &'a str) -> MaybeParseResult<Self::State,&'a str> {
// // ///         // ... parser goes here...`
// // /// #       fn is_lparen(ch: char) -> bool { ch == '(' }
// // /// #       fn is_rparen(ch: char) -> bool { ch == ')' }
// // /// #       fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
// // /// #       fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
// // /// #       fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
// // /// #       fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Tree {
// // /// #           Tree(children)
// // /// #       }
// // /// #       fn mk_box<P>(parser: P) -> TreeParserState
// // /// #       where P: 'static+for<'a> Stateful<&'a str, Output=Result<Tree,String>> {
// // /// #           Box::new(parser.boxable())
// // /// #       }
// // /// #       let LPAREN = character(is_lparen);
// // /// #       let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
// // /// #       let parser = LPAREN
// // /// #           .and_then_try(TreeParser.star(mk_vec))
// // /// #           .try_and_then_try(RPAREN)
// // /// #           .try_map3(mk_tree);
// // /// #       parser.parse(data).map(mk_box)
// // ///     }
// // /// }
// // /// ```
// // ///
// // /// The important thing is that the definiton of `parse` can make use of `TREE`, so the parser can call itself
// // /// recursively, then box up the result state:
// // ///
// // /// ```
// // /// # use parsell::{character,CHARACTER,Parser,Uncommitted,Committed,Boxable,Stateful,MaybeParseResult,Static};
// // /// # use parsell::ParseResult::{Done,Continue};
// // /// # use parsell::MaybeParseResult::{Commit};
// // /// # #[derive(Eq,PartialEq,Clone,Debug)]
// // /// struct Tree(Vec<Tree>);
// // /// impl Static for Tree {}
// // /// # #[derive(Copy,Clone,Debug)]
// // /// struct TreeParser;
// // /// type TreeParserState = Box<for<'b> Boxable<&'b str, Output=Result<Tree,String>>>;
// // /// impl Parser<char> for TreeParser {
// // ///     type StaticOutput = Result<Tree,String>;
// // ///     type State = TreeParserState;
// // /// }
// // /// impl<'a> Uncommitted<&'a str> for TreeParser {
// // ///     fn parse(&self, data: &'a str) -> MaybeParseResult<Self::State,&'a str> {
// // ///         fn is_lparen(ch: char) -> bool { ch == '(' }
// // ///         fn is_rparen(ch: char) -> bool { ch == ')' }
// // ///         fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
// // ///         fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
// // ///         fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
// // ///         fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Tree {
// // ///             Tree(children)
// // ///         }
// // ///         fn mk_box<P>(parser: P) -> TreeParserState
// // ///         where P: 'static+for<'a> Stateful<&'a str, Output=Result<Tree,String>> {
// // ///             Box::new(parser.boxable())
// // ///         }
// // ///         let LPAREN = character(is_lparen);
// // ///         let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
// // ///         let parser = LPAREN
// // ///             .and_then_try(TreeParser.star(mk_vec))
// // ///             .try_and_then_try(RPAREN)
// // ///             .try_map3(mk_tree);
// // ///         parser.parse(data).map(mk_box)
// // ///     }
// // /// }
// // /// let TREE = TreeParser;
// // /// match TREE.parse("((") {
// // ///     Commit(Continue("",parsing)) => match parsing.parse(")()))") {
// // ///         Done(")",result) => assert_eq!(result,Ok(Tree(vec![Tree(vec![]),Tree(vec![])]))),
// // ///          _ => panic!("can't happen"),
// // ///     },
// // ///     _ => panic!("can't happen"),
// // /// }
// // /// ```
// // ///
// // /// The reason for making `Boxable<S>` a different trait from `Stateful<S>`
// // /// is that it provides weaker safety guarantees. `Stateful<S>` enforces that
// // /// clients cannot call `parse` after `done`, but `Boxable<S>` does not.

pub trait Boxable<Ch, Str> 
    where Str: Iterator<Item = Ch>,
{
    type Output;
    fn more_boxable(&mut self, ch: Ch, string: Str) -> ParseResult<Ch, Str, (), Self::Output>;
    fn done_boxable(&mut self) -> Self::Output;
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

// /// A trait for consumers of data, typically buffers.
// ///
// /// # Examples
// ///
// /// `String` is a consumer of `&str` and of `char`.
// ///
// /// ```
// /// # use parsell::Consumer;
// /// let mut buffer = String::new();
// /// buffer.accept("abc");
// /// buffer.accept('d');
// /// assert_eq!(buffer,"abcd");
// /// ```
// ///
// /// `Vec<T>` is a consumer of `&[T]` when `T` is `Clone`, and of `T`.
// ///
// /// ```
// /// # use parsell::Consumer;
// /// let mut buffer = Vec::new();
// /// buffer.accept(&[1,2,3][..]);
// /// buffer.accept(4);
// /// assert_eq!(buffer,&[1,2,3,4]);
// /// ```
// ///
// /// The unit type `()` is a trivial consumer that discards data.
// ///
// /// ```
// /// # use parsell::Consumer;
// /// let mut discarder = ();
// /// discarder.accept("this");
// /// discarder.accept(4);
// /// assert_eq!(discarder,());
// /// ```

// pub trait Consumer<T> {
//     /// Accepts data.
//     fn accept(&mut self, value: T);
// }

// impl<T> Consumer<T> for () {
//     fn accept(&mut self, _: T) {}
// }

// impl Consumer<String> for String {
//     fn accept(&mut self, arg: String) {
//         self.push_str(&*arg);
//     }
// }

// impl<'a> Consumer<&'a str> for String {
//     fn accept(&mut self, arg: &'a str) {
//         self.push_str(arg);
//     }
// }

// impl Consumer<char> for String {
//     fn accept(&mut self, x: char) {
//         self.push(x);
//     }
// }

// impl<'a, T> Consumer<&'a [T]> for Vec<T> where T: Clone
// {
//     fn accept(&mut self, arg: &'a [T]) {
//         self.extend(arg.iter().cloned());
//     }
// }

// impl<T> Consumer<T> for Vec<T> {
//     fn accept(&mut self, x: T) {
//         self.push(x);
//     }
// }

// impl<C, T, E> Consumer<Result<T, E>> for Result<C, E> where C: Consumer<T>
// {
//     fn accept(&mut self, value: Result<T, E>) {
//         let err = match *self {
//             Err(_) => return,
//             Ok(ref mut consumer) => {
//                 match value {
//                     Err(err) => err,
//                     Ok(value) => return consumer.accept(value),
//                 }
//             }
//         };
//         *self = Err(err);
//     }
// }

/// A trait for subtyping

pub trait Upcast<T:?Sized> {
    fn upcast(self) -> T where Self: Sized;
}

impl<'a, T: ?Sized> Upcast<Cow<'a, T>> for Cow<'static, T>
    where T: ToOwned,
{
    fn upcast(self) -> Cow<'a, T> { self }
}

impl<S1, S2, T1, T2> Upcast<(T1, T2)> for (S1,S2)
    where S1: Upcast<T1>,
          S2: Upcast<T2>,
{
    fn upcast(self) -> (T1, T2) { (self.0.upcast(), self.1.upcast()) }
}

impl<S, T> Upcast<Option<T>> for Option<S>
    where S: Upcast<T>,
{
    fn upcast(self) -> Option<T> { self.map(Upcast::upcast) }
}

impl<S, T, D, E> Upcast<Result<T,E>> for Result<S,D>
    where S: Upcast<T>,
          D: Upcast<E>,
{
    fn upcast(self) -> Result<T,E> { self.map(Upcast::upcast).map_err(Upcast::upcast) }
}

/// A trait for data which can be saved to and restored from long-lived state.
///
/// The canonical example of this trait is `Cow<'a,T>` which can be saved to
/// and restored from `Cow<'static,T>` when `T` is static.

pub trait ToStatic {
    type Static: 'static;
    fn to_static(self) -> Self::Static where Self: Sized;
}

impl<'a, T: ?Sized> ToStatic for Cow<'a, T>
    where T: 'static + ToOwned
{
    type Static = Cow<'static, T>;
    fn to_static(self) -> Self::Static { Cow::Owned(self.into_owned()) }
}

impl<T, U> ToStatic for (T, U)
    where T: ToStatic,
          U: ToStatic
{
    type Static = (T::Static, U::Static);
    fn to_static(self) -> Self::Static { (self.0.to_static(), self.1.to_static()) }
}

impl<T> ToStatic for Option<T>
    where T: ToStatic
{
    type Static = Option<T::Static>;
    fn to_static(self) -> Self::Static { self.map(ToStatic::to_static) }
}

impl<T,E> ToStatic for Result<T,E> where T: ToStatic, E: ToStatic {
    type Static = Result<T::Static,E::Static>;
    fn to_static(self) -> Self::Static { self.map(ToStatic::to_static).map_err(ToStatic::to_static) }
}

/// A marker trait for static data.
///
/// This trait is a quick way to implment `ToStatic` as a no-op.

pub trait StaticMarker {}

impl<T> Upcast<T> for T where T: StaticMarker {
    fn upcast(self) -> T { self }
}

impl<T> ToStatic for T where T: 'static + StaticMarker {
    type Static = T;
    fn to_static(self) -> T { self }
}

impl StaticMarker for usize {}
impl StaticMarker for u8 {}
impl StaticMarker for u16 {}
impl StaticMarker for u32 {}
impl StaticMarker for u64 {}
impl StaticMarker for isize {}
impl StaticMarker for i8 {}
impl StaticMarker for i16 {}
impl StaticMarker for i32 {}
impl StaticMarker for i64 {}
impl StaticMarker for () {}
impl StaticMarker for bool {}
impl StaticMarker for char {}
impl StaticMarker for String {}
impl<T> StaticMarker for Vec<T> where T: 'static {}

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

// /// A committed parser that reads zero characters.

// pub fn emit<T>(t: T) -> impls::Return<T> {
//     impls::Return::new(t)
// }

// ----------- Tests -------------

#[allow(non_snake_case)]
impl<Ch, Str, State, Output> ParseResult<Ch, Str, State, Output> 
{
    pub fn unDone(self) -> (Ch, Str, Output) {
        match self {
            Done(ch, string, result) => (ch, string, result),
            _ => panic!("Not done"),
        }
    }

    pub fn unContinue(self) -> (Str, State) {
        match self {
            Continue(empty, state) => (empty, state),
            _ => panic!("Not continue"),
        }
    }
}

#[allow(non_snake_case)]
impl<Ch, Str, State, Output> MaybeParseResult<Ch, Str, State, Output> {

    pub fn unBacktrack(self) -> (Ch, Str) {
        match self { 
            Backtrack(ch, string) => (ch, string),
            _ => panic!("Not backtracking."),
        }
    }

    pub fn unCommit(self) -> ParseResult<Ch, Str, State, Output> {
        match self { 
            Commit(res) => res,
            _ => panic!("Not committed."),
        }
    }

}

#[test]
fn test_character() {
    let parser = character(char::is_alphabetic);
    assert!(parser.init_iter_maybe("".chars()).is_none());
    let (ch, iter) = parser.init_iter_maybe("989".chars()).unwrap().unBacktrack();
    assert_eq!(ch, '9');
    assert_eq!(iter.as_str(), "89");
    let (ch, iter, res) = parser.init_iter_maybe("abcd".chars()).unwrap().unCommit().unDone();
    assert_eq!(res, 'a');
    assert_eq!(ch, 'b');
    assert_eq!(iter.as_str(), "cd");
}

#[test]
fn test_character_ref() {
    fn is_alphabetic<'a>(ch: &'a char) -> bool { ch.is_alphabetic() }
    let parser = character_ref(is_alphabetic);
    assert!(parser.init_iter_maybe("".chars()).is_none());
    let (ch, iter) = parser.init_iter_maybe("989".chars()).unwrap().unBacktrack();
    assert_eq!(ch, '9');
    assert_eq!(iter.as_str(), "89");
    let (ch, iter, res) = parser.init_iter_maybe("abcd".chars()).unwrap().unCommit().unDone();
    assert_eq!(res, 'a');
    assert_eq!(ch, 'b');
    assert_eq!(iter.as_str(), "cd");
}

#[test]
#[allow(non_snake_case)]
fn test_CHARACTER() {
    let parser = CHARACTER;
    assert!(parser.init_iter("".chars()).is_none());
    let (ch, iter, res) = parser.init_iter("abcd".chars()).unwrap().unDone();
    assert_eq!(res, Some('a'));
    assert_eq!(ch, 'b');
    assert_eq!(iter.as_str(), "cd");
}

// #[test]
// fn test_emit() {
//     let parser = emit(37);
//     let iter = parser.init_str("".chars()).unEmpty();
//     assert_eq!(iter.as_str(), "");
//     let (ch, iter, res) = parser.init_str("abcd".chars()).unCommit().unDone();
//     assert_eq!(res, 37);
//     assert_eq!(ch, 'a');
//     assert_eq!(iter.as_str(), "bcd");
// }

#[test]
fn test_map1() {
    // uncommitted map
    let parser = character(char::is_alphabetic).map(Some);
    assert!(parser.init_iter_maybe("".chars()).is_none());
    let (ch, iter) = parser.init_iter_maybe("989".chars()).unwrap().unBacktrack();
    assert_eq!(ch, '9');
    assert_eq!(iter.as_str(), "89");
    let (ch, iter, res) = parser.init_iter_maybe("abcd".chars()).unwrap().unCommit().unDone();
    assert_eq!(res, Some('a'));
    assert_eq!(ch, 'b');
    assert_eq!(iter.as_str(), "cd");
    // committed map
    let parser = CHARACTER.map(Some);
    assert!(parser.init_iter("".chars()).is_none());
    let (ch, iter, res) = parser.init_iter("abcd".chars()).unwrap().unDone();
    assert_eq!(res, Some(Some('a')));
    assert_eq!(ch, 'b');
    assert_eq!(iter.as_str(), "cd");
}

// #[test]
// fn test_map2() {
//     let parser = CHARACTER.map(Some);
//     let iter = parser.init_str("".chars()).unEmpty();
//     assert_eq!(iter.as_str(), "");
//     let (ch, iter, res) = parser.init_str("abcd".chars()).unCommit().unDone();
//     assert_eq!(res, Some(Some('a')));
//     assert_eq!(ch, 'b');
//     assert_eq!(iter.as_str(), "cd");
// }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_map2() {
// //     fn f(ch1: char, ch2: Option<char>) -> Option<(char, char)> {
// //         ch2.and_then(|ch2| Some((ch1, ch2)))
// //     }
// //     fn mk_none<T>(_: Option<char>) -> Option<T> {
// //         None
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
// //     let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).map2(f);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("!b!").unAbort(), "!b!");
// //     assert_eq!(parser.parse("a!!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("ab!").unCommit().unDone(),
// //                ("!", Some(('a', 'b'))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_map3() {
// //     fn f(ch1: char, ch2: Option<char>, ch3: Option<char>) -> Option<(char, char, char)> {
// //         ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1, ch2, ch3))))
// //     }
// //     fn mk_none<T>(_: Option<char>) -> Option<T> {
// //         None
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
// //     let parser = character(char::is_alphabetic)
// //                      .and_then(ALPHANUMERIC)
// //                      .and_then(ALPHANUMERIC)
// //                      .map3(f);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("!bc!").unAbort(), "!bc!");
// //     assert_eq!(parser.parse("a!c!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("ab!!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("abc!").unCommit().unDone(),
// //                ("!", Some(('a', 'b', 'c'))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_map4() {
// //     fn f(ch1: char,
// //          ch2: Option<char>,
// //          ch3: Option<char>,
// //          ch4: Option<char>)
// //          -> Option<(char, char, char, char)> {
// //         ch4.and_then(|ch4| ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1, ch2, ch3, ch4)))))
// //     }
// //     fn mk_none<T>(_: Option<char>) -> Option<T> {
// //         None
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
// //     let parser = character(char::is_alphabetic)
// //                      .and_then(ALPHANUMERIC)
// //                      .and_then(ALPHANUMERIC)
// //                      .and_then(ALPHANUMERIC)
// //                      .map4(f);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("!bcd!").unAbort(), "!bcd!");
// //     assert_eq!(parser.parse("a!cd!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("ab!d!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("abc!!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("abcd!").unCommit().unDone(),
// //                ("!", Some(('a', 'b', 'c', 'd'))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_map5() {
// //     fn f(ch1: char,
// //          ch2: Option<char>,
// //          ch3: Option<char>,
// //          ch4: Option<char>,
// //          ch5: Option<char>)
// //          -> Option<(char, char, char, char, char)> {
// //         ch5.and_then(|ch5| {
// //             ch4.and_then(|ch4| {
// //                 ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1, ch2, ch3, ch4, ch5))))
// //             })
// //         })
// //     }
// //     fn mk_none<T>(_: Option<char>) -> Option<T> {
// //         None
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
// //     let parser = character(char::is_alphabetic)
// //                      .and_then(ALPHANUMERIC)
// //                      .and_then(ALPHANUMERIC)
// //                      .and_then(ALPHANUMERIC)
// //                      .and_then(ALPHANUMERIC)
// //                      .map5(f);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("!bcde!").unAbort(), "!bcde!");
// //     assert_eq!(parser.parse("a!cde!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("ab!de!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("abc!e!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("abcd!!").unCommit().unDone(), ("!", None));
// //     assert_eq!(parser.parse("abcde!").unCommit().unDone(),
// //                ("!", Some(('a', 'b', 'c', 'd', 'e'))));
// // }

#[test]
#[allow(non_snake_case)]
fn test_and_then() {
    // uncommitted
    let parser = character(char::is_alphabetic).and_then(CHARACTER);
    let (ch, iter) = parser.init_iter_maybe("989".chars()).unwrap().unBacktrack();
    assert_eq!(ch, '9');
    assert_eq!(iter.as_str(), "89");
    let (ch, iter, res) = parser.init_iter_maybe("abcd".chars()).unwrap().unCommit().unDone();
    assert_eq!(res, ('a', Some('b')));
    assert_eq!(ch, 'c');
    assert_eq!(iter.as_str(), "d");
    // committed
    let parser = CHARACTER.and_then(CHARACTER);
    let (ch, iter, res) = parser.init_iter("abcd".chars()).unwrap().unDone();
    assert_eq!(res, (Some('a'), Some('b')));
    assert_eq!(ch, 'c');
    assert_eq!(iter.as_str(), "d");
}

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_try_and_then() {
// //     fn mk_err<T>(_: Option<char>) -> Result<T, String> {
// //         Err(String::from("oh"))
// //     }
// //     fn mk_ok<T>(ok: T) -> Result<T, String> {
// //         Ok(ok)
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
// //     let parser = character(char::is_alphabetic).map(mk_ok).try_and_then(ALPHANUMERIC);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("989").unAbort(), "989");
// //     assert_eq!(parser.parse("a!!").unCommit().unDone(),
// //                ("!", Ok(('a', Err(String::from("oh"))))));
// //     assert_eq!(parser.parse("abc").unCommit().unDone(),
// //                ("c", Ok(('a', Ok('b')))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_and_then_try() {
// //     fn mk_err<T>(_: Option<char>) -> Result<T, String> {
// //         Err(String::from("oh"))
// //     }
// //     fn mk_ok<T>(ok: T) -> Result<T, String> {
// //         Ok(ok)
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
// //     let parser = character(char::is_alphabetic).map(mk_ok).and_then_try(ALPHANUMERIC);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("989").unAbort(), "989");
// //     assert_eq!(parser.parse("a!!").unCommit().unDone(),
// //                ("!", Err(String::from("oh"))));
// //     assert_eq!(parser.parse("abc").unCommit().unDone(),
// //                ("c", Ok((Ok('a'), 'b'))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_try_and_then_try() {
// //     fn mk_err<T>(_: Option<char>) -> Result<T, String> {
// //         Err(String::from("oh"))
// //     }
// //     fn mk_ok<T>(ok: T) -> Result<T, String> {
// //         Ok(ok)
// //     }
// //     let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
// //     let parser = character(char::is_alphabetic).map(mk_ok).try_and_then_try(ALPHANUMERIC);
// //     parser.parse("").unEmpty();
// //     assert_eq!(parser.parse("989").unAbort(), "989");
// //     assert_eq!(parser.parse("a!!").unCommit().unDone(),
// //                ("!", Err(String::from("oh"))));
// //     assert_eq!(parser.parse("abc").unCommit().unDone(),
// //                ("c", Ok(('a', 'b'))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_or_else() {
// //     fn mk_none<T>(_: Option<char>) -> Option<T> {
// //         None
// //     }
// //     let NUMERIC = character(char::is_numeric).map(Some).or_else(CHARACTER.map(mk_none));
// //     let ALPHABETIC = character(char::is_alphabetic).map(Some).or_else(CHARACTER.map(mk_none));
// //     let parser = character(char::is_alphabetic)
// //                      .and_then(ALPHABETIC)
// //                      .map(Some)
// //                      .or_else(character(char::is_numeric).and_then(NUMERIC).map(Some))
// //                      .or_else(CHARACTER.map(mk_none));
// //     parser.init().parse("").unContinue();
// //     parser.init().parse("a").unContinue();
// //     parser.init().parse("9").unContinue();
// //     assert_eq!(parser.init().parse("!!").unDone(), ("!", None));
// //     assert_eq!(parser.init().parse("a99").unDone(),
// //                ("9", Some(('a', None))));
// //     assert_eq!(parser.init().parse("9aa").unDone(),
// //                ("a", Some(('9', None))));
// //     assert_eq!(parser.init().parse("abc").unDone(),
// //                ("c", Some(('a', Some('b')))));
// //     assert_eq!(parser.init().parse("123").unDone(),
// //                ("3", Some(('1', Some('2')))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_plus() {
// //     let parser = character(char::is_alphanumeric).plus(String::new);
// //     parser.parse("").unEmpty();
// //     parser.parse("!!!").unAbort();
// //     assert_eq!(parser.parse("a!").unCommit().unDone(),
// //                ("!", String::from("a")));
// //     assert_eq!(parser.parse("abc98def!").unCommit().unDone(),
// //                ("!", String::from("abc98def")));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_star() {
// //     let parser = character(char::is_alphanumeric).star(String::new);
// //     parser.init().parse("").unContinue();
// //     assert_eq!(parser.init().parse("!!!").unDone(),
// //                ("!!!", String::from("")));
// //     assert_eq!(parser.init().parse("a!").unDone(), ("!", String::from("a")));
// //     assert_eq!(parser.init().parse("abc98def!").unDone(),
// //                ("!", String::from("abc98def")));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_buffer() {
// //     use std::borrow::Cow::{Borrowed, Owned};
// //     fn ignore() {}
// //     let ALPHABETIC = character(char::is_alphabetic);
// //     let ALPHANUMERIC = character(char::is_alphanumeric);
// //     let parser = ALPHABETIC.and_then(ALPHANUMERIC.star(ignore)).buffer();
// //     assert_eq!(parser.parse("989").unAbort(), "989");
// //     assert_eq!(parser.parse("a!").unCommit().unDone(), ("!", Borrowed("a")));
// //     assert_eq!(parser.parse("abc!").unCommit().unDone(),
// //                ("!", Borrowed("abc")));
// //     let parsing = parser.parse("a").unCommit().unContinue();
// //     assert_eq!(parsing.parse("bc!").unDone(),
// //                ("!", Owned(String::from("abc"))));
// //     let parser = ALPHANUMERIC.star(ignore).buffer();
// //     assert_eq!(parser.init().parse("!").unDone(), ("!", Borrowed("")));
// //     assert_eq!(parser.init().parse("a!").unDone(), ("!", Borrowed("a")));
// //     assert_eq!(parser.init().parse("abc!").unDone(), ("!", Borrowed("abc")));
// //     let parsing = parser.init().parse("a").unContinue();
// //     assert_eq!(parsing.parse("bc!").unDone(),
// //                ("!", Owned(String::from("abc"))));
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_cow() {
// //     fn is_foo<'a>(string: &Cow<'a,str>) -> bool { string == "foo" }
// //     fn mk_other<'a>(_: Option<Cow<'a,str>>) -> Cow<'a,str> { Cow::Borrowed("other") }
// //     fn is_owned<'a,T:?Sized+ToOwned>(cow: Cow<'a,T>) -> bool { match cow { Cow::Owned(_) => true, _ => false } }
// //     let ONE = character_ref(is_foo);
// //     let OTHER = CHARACTER.map(mk_other);
// //     let parser = ONE.and_then(ONE.or_else(OTHER)).and_then(ONE.or_else(OTHER));
// //     let mut data = vec!["foo","bar","foo","baz"];
// //     let (ch, _, ((fst, snd), thd)) = parser.maybe_str(data.drain(..).map(Cow::Borrowed)).unCommit().unDone();
// //     assert_eq!(ch, "baz");
// //     assert_eq!(fst, "foo");
// //     assert_eq!(snd, "other");
// //     assert_eq!(thd, "foo");
// //     assert!(!is_owned(fst));
// //     assert!(!is_owned(snd));
// //     assert!(!is_owned(thd));
// //     let mut data1 = vec!["foo","bar"];
// //     let mut data2 = vec!["foo","baz"];
// //     let (_, parsing) = parser.maybe_str(data1.drain(..).map(Cow::Borrowed)).unCommit().unContinue();
// //     let (ch, _, ((fst, snd), thd)) = parsing.more_str(data2.drain(..).map(Cow::Borrowed)).unDone();
// //     assert_eq!(ch, "baz");
// //     assert_eq!(fst, "foo");
// //     assert_eq!(snd, "other");
// //     assert_eq!(thd, "foo");
// //     assert!(is_owned(fst));
// //     assert!(!is_owned(snd));
// //     assert!(!is_owned(thd));
// //     let mut data1 = vec!["foo","foo"];
// //     let mut data2 = vec!["foo","baz"];
// //     let (_, parsing) = parser.maybe_str(data1.drain(..).map(Cow::Borrowed)).unCommit().unContinue();
// //     let (ch, _, ((fst, snd), thd)) = parsing.more_str(data2.drain(..).map(Cow::Borrowed)).unDone();
// //     assert_eq!(ch, "baz");
// //     assert_eq!(fst, "foo");
// //     assert_eq!(snd, "foo");
// //     assert_eq!(thd, "foo");
// //     assert!(is_owned(fst));
// //     assert!(is_owned(snd));
// //     assert!(!is_owned(thd));
// //     let mut data1 = vec!["foo","bar","foo"];
// //     let mut data2 = vec!["baz"];
// //     let (_, parsing) = parser.maybe_str(data1.drain(..).map(Cow::Borrowed)).unCommit().unContinue();
// //     let (ch, _, ((fst, snd), thd)) = parsing.more_str(data2.drain(..).map(Cow::Borrowed)).unDone();
// //     assert_eq!(ch, "baz");
// //     assert_eq!(fst, "foo");
// //     assert_eq!(snd, "other");
// //     assert_eq!(thd, "foo");
// //     assert!(is_owned(fst));
// //     assert!(is_owned(snd));
// //     assert!(is_owned(thd));
// // }

// #[derive(Copy, Clone, Debug)]
// pub struct CharacterState<Ch>(Ch);

// impl<Str, Ch, StaticCh> Stateful<Str> for CharacterState<StaticCh>
//     where Str: Iterator<Item = Ch>,
//           StaticCh: Cast<Ch>,
// {
//     type Output = Ch;

//     fn more_ch_str(self, ch: Ch, string: Str) -> StatefulParseChStrResult<Self, Str> {
//         Done((ch, string, self.0.cast()))
//     }

//     fn more_eof(self) -> Str::Item {
//         self.0.cast()
//     }
// }

// trait Cast<T> {
//     fn cast(self) -> T;
// }
// impl<'a,T:?Sized> Cast<Cow<'a,T>> for Cow<'static,T>
//     where T: ToOwned
// {
//     fn cast(self) -> Cow<'a,T> { self }
// }

// trait Stateful2<Ch,Str> where Str: Iterator<Item=Ch> {
//     type Output;
//     fn more_ch_str(self, ch: Ch, string: Str);
//     fn more_eof(self) -> Ch;
// }

// impl<Str, Ch, StaticCh> Stateful2<Ch,Str> for CharacterState<StaticCh>
//     where Str: Iterator<Item = Ch>,
//           StaticCh: Cast<Ch>,
// {
//     type Output = Ch;

//     fn more_ch_str(self, ch: Ch, string: Str) {
//     }

//     fn more_eof(self) -> Str::Item {
//         self.0.cast()
//     }
// }

#[test]
#[allow(non_snake_case)]
fn test_boxable() {
    use std::vec::Drain;
    #[derive(Copy, Clone, Debug)]
    struct Test;
    type TestCh<'a> = Cow<'a,str>;
    type TestStr<'a> = Drain<'a,TestCh<'a>>;
    type TestOutput<'a> = (TestCh<'a>, TestCh<'a>); //Cow<'a,str>;//((Cow<'a,str>, Cow<'a,str>), Cow<'a,str>);
    type TestState = Box<for<'a> Boxable<TestCh<'a>, TestStr<'a>, Output=TestOutput<'a>>>;
    impl Parser for Test {}
    impl<'a> Uncommitted<TestCh<'a>, TestStr<'a>> for Test {
        type Output = TestOutput<'a>;
        type State = TestState;
        fn init_maybe(&self, ch: TestCh<'a>, string: TestStr<'a>) -> MaybeParseResult<TestCh<'a>, TestStr<'a>, TestState, TestOutput<'a>> {
            fn is_foo<'a>(string: &Cow<'a,str>) -> bool { string == "foo" }
            fn mk_other<'a>(_: Option<TestCh<'a>>) -> TestCh<'a> { Cow::Borrowed("other") }
            fn is_owned<'a,T:?Sized+ToOwned>(cow: Cow<'a,T>) -> bool { match cow { Cow::Owned(_) => true, _ => false } }
            let ONE = character_ref(is_foo);
            let OTHER = CHARACTER.map(mk_other);
            let parser = ONE.and_then(OTHER);//ONE.and_then(ONE.or_else(OTHER)).and_then(ONE.or_else(OTHER));
            fn foo<P>(state: P) -> P
                where P: for<'a> Stateful<TestCh<'a>, TestStr<'a>, Output=TestOutput<'a>>
            {
                state
            }
            fn bar<P>(state: P) -> P
                where P: for<'a> Boxable<TestCh<'a>, TestStr<'a>, Output=TestOutput<'a>>
            {
                state
            }
            // This bit should be in the API
            match parser.init_maybe(ch, string) {
                Backtrack(ch, string) => Backtrack(ch, string),
                Commit(Done(ch, string, result)) => Commit(Done(ch, string, result)),
                Commit(Continue(empty, state)) => {
                    let state = foo(state);
                    let boxable = bar(impls::BoxableState::new(state));
                    let boxed: TestState = Box::new(boxable);
                    Commit(Continue(empty, boxed))
                },
            }
        }
    }
    // let data = [1,2,1,4];
    // let (ch, _, ((fst, snd), thd)) = parser.maybe_str(data.iter()).unCommit().unDone();
    // assert_eq!(*ch, 4);
    // assert_eq!(fst, "one");
    // assert_eq!(snd, "other");
    // assert_eq!(thd, "one");
    // assert!(!is_owned(fst));
    // assert!(!is_owned(snd));
    // assert!(!is_owned(thd));
    // let data1 = [1,2];
    // let data2 = [1,4];
    // let (_, parsing) = parser.maybe_str(data1.iter()).unCommit().unContinue();
    // let (ch, _, ((fst, snd), thd)) = parsing.more_str(data2.iter()).unDone();
    // assert_eq!(*ch, 4);
    // assert_eq!(fst, "one");
    // assert_eq!(snd, "other");
    // assert_eq!(thd, "one");
    // assert!(is_owned(fst));
    // assert!(!is_owned(snd));
    // assert!(!is_owned(thd));
    // let data1 = [1,2,1];
    // let data2 = [4];
    // let (_, parsing) = parser.maybe_str(data1.iter()).unCommit().unContinue();
    // let (ch, _, ((fst, snd), thd)) = parsing.more_str(data2.iter()).unDone();
    // assert_eq!(*ch, 4);
    // assert_eq!(fst, "one");
    // assert_eq!(snd, "other");
    // assert_eq!(thd, "one");
    // assert!(is_owned(fst));
    // assert!(is_owned(snd));
    // assert!(!is_owned(thd));
}

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

// // // #[test]
// // // #[allow(non_snake_case)]
// // // fn test_pipe() {
// // //     use std::borrow::{Borrow, Cow};
// // //     #[derive(Clone,Debug,PartialEq,Eq)]
// // //     enum Token {
// // //         Identifier(String),
// // //         Number(usize),
// // //         Other,
// // //     }
// // //     fn mk_id<'a>(string: Cow<'a, str>) -> Token {
// // //         Token::Identifier(string.into_owned())
// // //     }
// // //     fn mk_num<'a>(string: Cow<'a, str>) -> Token {
// // //         Token::Number(usize::from_str_radix(string.borrow(), 10).unwrap())
// // //     }
// // //     fn mk_other(_: Option<char>) -> Token {
// // //         Token::Other
// // //     }
// // //     fn ignore() {}
// // //     fn is_decimal(ch: char) -> bool {
// // //         ch.is_digit(10)
// // //     }
// // //     fn is_identifier(tok: &Token) -> bool {
// // //         match *tok {
// // //             Token::Identifier(_) => true,
// // //             _ => false,
// // //         }
// // //     }
// // //     fn is_number(tok: &Token) -> bool {
// // //         match *tok {
// // //             Token::Number(_) => true,
// // //             _ => false,
// // //         }
// // //     }
// // //     let ALPHABETIC = character(char::is_alphabetic);
// // //     let DIGIT = character(is_decimal);
// // //     let lexer = ALPHABETIC.plus(ignore)
// // //                           .buffer()
// // //                           .map(mk_id)
// // //                           .or_else(DIGIT.plus(ignore).buffer().map(mk_num))
// // //                           .or_else(CHARACTER.map(mk_other));
// // //     let parser = token(is_identifier).or_else(token(is_number)).star(Vec::<Token>::new);
// // //     assert_eq!(lexer.pipe(parser).init().parse("abc37!!").unDone(),
// // //                ("!",
// // //                 vec![Token::Identifier(String::from("abc")), Token::Number(37)]));
// // // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_different_lifetimes1() {
// //     fn go<'a, 'b, P>(ab: &'a str, cd: &'b str, parser: P)
// //         where P: Copy + Parser<char> + for<'c> Committed<&'c str>,
// //               <P as Parser<char>>::State: for<'c> Stateful<&'c str, Output = (Option<char>, Option<char>)>,
// //     {
// //         let _: &'a str = parser.init().parse(ab).unDone().0;
// //         let _: &'b str = parser.init().parse(cd).unDone().0;
// //         assert_eq!(parser.init().parse(ab).unDone(),
// //                    ("", (Some('a'), Some('b'))));
// //         assert_eq!(parser.init().parse(cd).unDone(),
// //                    ("", (Some('c'), Some('d'))));
// //     }
// //     let parser = CHARACTER.and_then(CHARACTER);
// //     go("ab", "cd", parser);
// // }

// // #[test]
// // #[allow(non_snake_case)]
// // fn test_different_lifetimes2() {
// //     use std::borrow::Cow;
// //     use std::borrow::Cow::Owned;
// //     fn ignore() {}
// //     fn is_owned<'a,T:?Sized+ToOwned>(cow: &Cow<'a,T>) -> bool { match cow { &Owned(_) => true, _ => false } }
// //     let parser = character(char::is_alphabetic).star(ignore).buffer()
// //         .and_then(character(char::is_numeric).star(ignore).buffer());
// //     match parser.init().parse("abc123!") {
// //         Done("!", (ref fst, ref snd)) => {
// //             assert!(!is_owned(fst));
// //             assert!(!is_owned(snd));
// //             assert_eq!(fst, "abc");
// //             assert_eq!(snd, "123");
// //         },
// //         oops => panic!("Shouldn't happen {:?}", oops),
// //     };
// //     match parser.init().parse("abc1").unContinue().parse("23!") {
// //         Done("!", (ref fst, ref snd)) => {
// //             assert!(is_owned(fst));
// //             assert!(is_owned(snd));
// //             assert_eq!(fst, "abc");
// //             assert_eq!(snd, "123");
// //         },
// //         oops => panic!("Shouldn't happen {:?}", oops),
// //     };
// // }
