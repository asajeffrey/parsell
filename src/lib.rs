//! Parsimonious: a parser combinator library for Rust
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
//! [Repo](https://github.com/asajeffrey/parsimonious) |
//! [Crate](https://crates.io/crates/parsimonious) |
//! [CI](https://travis-ci.org/asajeffrey/parsimonious)

use self::GuardedParseResult::{Empty,Abort,Commit};
use self::ParseResult::{Done,Continue};

// ----------- Types for parsers ------------

/// A trait for stateful parsers.
///
/// Stateful parsers are typically constructed by calling the `init` method of a stateless parser,
/// for example:
///
/// ```
/// # use parsimonious::{character_guard,GuardedParserOf,ParserOf};
/// let stateless = character_guard(char::is_alphanumeric).star(String::new);
/// let stateful = stateless.init();
/// ```
///
/// Here, `stateless` is a `ParserOf<&str,Output=String>`, and `stateful` is a `StatefulParserOf<&str,Output=String>`.

pub trait StatefulParserOf<S> {

    /// The type of the data being produced by the parser.
    type Output;

    /// Provides data to the parser.
    ///
    /// If `parser: StatefulParserOf<S,Output=T>`, then `parser.parse(data)` either:
    ///
    /// * returns `Done(rest, result)` where `rest: S` is any remaining input,
    ///   and `result: T` is the parsed output, or
    /// * returns `Continue(parsing)` where `parsing: Self` is the new state of the parser.
    ///
    /// For example:
    ///
    /// ```
    /// # use parsimonious::{character_guard,GuardedParserOf,ParserOf,StatefulParserOf};
    /// # use parsimonious::ParseResult::{Continue,Done};
    /// let parser = character_guard(char::is_alphabetic).star(String::new);
    /// let stateful = parser.init();
    /// match stateful.parse("abc") {
    ///     Done(_,_) => panic!("can't happen"),
    ///     Continue(parsing) => match parsing.parse("def!") {
    ///         Continue(_) => panic!("can't happen"),
    ///         Done(rest,result) => {
    ///             assert_eq!(rest,"!");
    ///             assert_eq!(result,"abcdef");
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// Note that `parser.parse(data)` consumes both the `parser` and the `data`. In particular,
    /// the `parser` is no longer available, so the following does not typecheck:
    ///
    /// ```text
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// let stateful = parser.init();
    /// stateful.parse("abc");
    /// stateful.parse("def!");
    /// ```
    ///
    /// This helps with parser safety, as it stops a client from calling `parse` after a
    /// a stateful parser has finished.
    fn parse(self, value: S) -> ParseResult<Self,S> where Self: Sized;

    /// Tells the parser that it will not receive any more data.
    ///
    /// If `parser: StatefulParserOf<S,Output=T>`, then `parser.done()` returns a result of type `T`
    /// for example:
    ///
    /// ```
    /// # use parsimonious::{character_guard,GuardedParserOf,ParserOf,StatefulParserOf};
    /// # use parsimonious::ParseResult::{Continue,Done};
    /// let parser = character_guard(char::is_alphabetic).star(String::new);
    /// let stateful = parser.init();
    /// match stateful.parse("abc") {
    ///     Done(_,_) => panic!("can't happen"),
    ///     Continue(parsing) => match parsing.parse("def") {
    ///         Done(_,_) => panic!("can't happen"),
    ///         Continue(parsing) => assert_eq!(parsing.done(),"abcdef"),
    ///     }
    /// }
    /// ```
    ///
    /// Note that `parser.done()` consumes the `parser`. In particular,
    /// the `parser` is no longer available, so the following does not typecheck:
    ///
    /// ```text
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// let stateful = parser.init();
    /// stateful.done();
    /// stateful.parse("def!");
    /// ```
    ///
    /// This helps with parser safety, as it stops a client from calling `parse` after a
    /// a stateful parser has finished.
    fn done(self) -> Self::Output where Self: Sized;

    /// Make this parser boxable.
    fn boxable(self) -> impls::BoxableParser<Self> where Self: Sized { impls::BoxableParser::new(self) }

}

/// The result of a parse.
pub enum ParseResult<P,S> where P: StatefulParserOf<S> {
    /// The parse is finished.
    Done(S,P::Output),
    /// The parse can continue.
    Continue(P),
}

impl<P,S> ParseResult<P,S> where P: StatefulParserOf<S> {
    /// Apply a function the the `Continue` branch of a parse result.
    pub fn map<F,Q>(self, f: F) -> ParseResult<Q,S> where Q: StatefulParserOf<S,Output=P::Output>, F: Function<P,Output=Q> {
        match self {
            Done(rest,result) => Done(rest,result),
            Continue(parsing) => Continue(f.apply(parsing)),
        }
    }
}

/// A trait for stateless parsers.
///
/// Stateful parsers are typically constructed by calling the methods of the library,
/// for example:
///
/// ```
/// # use parsimonious::{character_guard,GuardedParserOf};
/// let stateless = character_guard(char::is_alphanumeric).star(String::new);
/// ```
///
/// Here, `stateless` is a `ParserOf<&str,Output=String>`.
///
/// The reason for distinguishing between stateful and stateless parsers is that
/// stateless parsers are usually copyable, whereas stateful parsers are not
/// (they may, for example, have created and partially filled some buffers).
/// Copying parsers is quite common, for example:
///
/// ```
/// # use parsimonious::{character,GuardedParserOf,ParserOf,StatefulParserOf};
/// # use parsimonious::ParseResult::Done;
/// let DIGIT = character(char::is_numeric);
/// let TWO_DIGITS = DIGIT.and_then(DIGIT);
/// match TWO_DIGITS.init().parse("123") {
///    Done(_,result) => assert_eq!(result,(Some('1'),Some('2'))),
///    _ => panic!("Can't happen"),
/// }
/// ```
///
/// Semantically, a parser with input *S* and output *T* is a partial function *S\* → T*
/// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain)
/// and non-empty.

pub trait ParserOf<S> {

    /// The type of the data being produced by the parser.
    type Output;

    /// The type of the parser state.
    type State: StatefulParserOf<S,Output=Self::Output>;

    /// Create a stateful parser by initializing a stateless parser.
    fn init(&self) -> Self::State;

    /// Sequencing with a parser (returns a parser).
    fn and_then<P>(self, other: P) -> impls::AndThenParser<Self,P> where Self:Sized, P: ParserOf<S> { impls::AndThenParser::new(self,other) }

    /// Sequencing with a parser (returns a parser, returns an error when this parser returns an error).
    fn try_and_then<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::TryZip> where Self:Sized, P: ParserOf<S> { self.and_then(other).map(impls::TryZip) }

    /// Sequencing with a parser (returns a parser, returns an error when the other parser returns an error).
    fn and_then_try<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::ZipTry> where Self:Sized, P: ParserOf<S> { self.and_then(other).map(impls::ZipTry) }

    /// Sequencing with a parser (returns a parser, returns an error when the other parser returns an error).
    fn try_and_then_try<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::TryZipTry> where Self:Sized, P: ParserOf<S> { self.and_then(other).map(impls::TryZipTry) }

    /// Apply a function to the result (returns a parser).
    fn map<F>(self, f: F) -> impls::MapParser<Self,F> where Self:Sized, { impls::MapParser::new(self,f) }

    /// Apply a 2-arguent function to the result (returns a parser).
    fn map2<F>(self, f: F) -> impls::MapParser<Self,impls::Function2<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function2::new(f)) }

    /// Apply a 3-arguent function to the result (returns a parser).
    fn map3<F>(self, f: F) -> impls::MapParser<Self,impls::Function3<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function3::new(f)) }

    /// Apply a 4-arguent function to the result (returns a parser).
    fn map4<F>(self, f: F) -> impls::MapParser<Self,impls::Function4<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function4::new(f)) }

    /// Apply a 5-arguent function to the result (returns a parser).
    fn map5<F>(self, f: F) -> impls::MapParser<Self,impls::Function5<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function5::new(f)) }

    /// Apply a function to the result (returns a parser, returns an error when this parser returns an error).
    fn try_map<F>(self, f: F) -> impls::MapParser<Self,impls::Try<F>> where Self:Sized, { self.map(impls::Try::new(f)) }

    /// Apply a 2-argument function to the result (returns a parser, returns an error when this parser returns an error).
    fn try_map2<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function2<F>>> where Self:Sized, { self.try_map(impls::Function2::new(f)) }

    /// Apply a 3-argument function to the result (returns a parser, returns an error when this parser returns an error).
    fn try_map3<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function3<F>>> where Self:Sized, { self.try_map(impls::Function3::new(f)) }

    /// Apply a 4-argument function to the result (returns a parser, returns an error when this parser returns an error).
    fn try_map4<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function4<F>>> where Self:Sized, { self.try_map(impls::Function4::new(f)) }

    /// Apply a 5-argument function to the result (returns a parser, returns an error when this parser returns an error).
    fn try_map5<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function5<F>>> where Self:Sized, { self.try_map(impls::Function5::new(f)) }

}

/// A trait for stateless guarded parsers.
///
/// A guarded parser can decide based on the first token of input whether
/// it will commit to parsing, or immediately backtrack and try another option.
///
/// The advantage of guarded parsers over parsers is they support choice:
/// `p.or_else(q)` will try `p`, and commit if it commits, but if it backtracks
/// will then try `q`; and `p.or_emit(f)` will try `p` and commit if it commits,
/// but if it backtracks will stop parsing and return `f()`. For example:
///
/// ```
/// # use parsimonious::{character_guard,GuardedParserOf,ParserOf,StatefulParserOf};
/// # use parsimonious::ParseResult::Done;
/// fn default_char() -> char { '?' }
/// let parser =
///    character_guard(char::is_numeric)
///        .or_else(character_guard(char::is_alphabetic))
///        .or_emit(default_char);
/// match parser.init().parse("123") {
///    Done(_,result) => assert_eq!(result,'1'),
///    _ => panic!("Can't happen"),
/// }
/// match parser.init().parse("abc") {
///    Done(_,result) => assert_eq!(result,'a'),
///    _ => panic!("Can't happen"),
/// }
/// match parser.init().parse("!@#") {
///    Done(_,result) => assert_eq!(result,'?'),
///    _ => panic!("Can't happen"),
/// }
/// ```
///
/// Semantically, a parser with input *S* and output *T* is a partial function *S\+ → T*
/// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain).

pub trait GuardedParserOf<S> {

    /// The type of the data being produced by the parser.
    type Output;

    /// The type of the parser state.
    type State: StatefulParserOf<S,Output=Self::Output>;

    /// Provides data to the parser.
    ///
    /// If `parser: StatefulParserOf<S,Output=T>`, then `parser.parse(data)` either:
    ///
    /// * returns `Empty` because `data` was empty,
    /// * returns `Abort(data)` because the parser should backtrack, or
    /// * returns `Commit(result)` because the parser has committed.
    ///
    /// For example:
    ///
    /// ```
    /// # use parsimonious::{character_guard,GuardedParserOf,StatefulParserOf};
    /// # use parsimonious::GuardedParseResult::{Empty,Commit,Abort};
    /// # use parsimonious::ParseResult::{Done,Continue};
    /// let parser = character_guard(char::is_alphabetic).plus(String::new);
    /// match parser.parse("") {
    ///     Empty => (),
    ///     _ => panic!("can't happen"),
    /// }
    /// match parser.parse("!abc") {
    ///     Abort("!abc") => (),
    ///     _ => panic!("can't happen"),
    /// }
    /// match parser.parse("abc!") {
    ///     Commit(Done("!",result)) => assert_eq!(result,"abc"),
    ///     _ => panic!("can't happen"),
    /// }
    /// match parser.parse("abc") {
    ///     Commit(Continue(parsing)) => match parsing.parse("def!") {
    ///         Done("!",result) => assert_eq!(result,"abcdef"),
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```
    ///
    /// Note that the decision to commit or abort must be made on the first
    /// token of data (since the parser only retries on empty input)
    /// so this is appropriate for LL(1) grammars that only perform one token
    /// of lookahead.
    fn parse(&self, value: S) -> GuardedParseResult<Self::State,S> where Self: Sized;

    /// Choice between guarded parsers (returns a guarded parser).
    fn or_else<P>(self, other: P) -> impls::OrElseGuardedParser<Self,P> where Self:Sized, P: GuardedParserOf<S> { impls::OrElseGuardedParser::new(self,other) }

    /// Gives a guarded parser a default value (returns a parser).
    fn or_emit<F>(self, factory: F) -> impls::OrEmitParser<Self,F> where Self:Sized { impls::OrEmitParser::new(self,factory) }

    /// Sequencing with a parser (returns a guarded parser).
    fn and_then<P>(self, other: P) -> impls::AndThenParser<Self,P> where Self:Sized, P: ParserOf<S> { impls::AndThenParser::new(self,other) }

    /// Sequencing with a parser (returns a guarded parser, returns an error when this parser returns an error).
    fn try_and_then<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::TryZip> where Self:Sized, P: ParserOf<S> { self.and_then(other).map(impls::TryZip) }

    /// Sequencing with a parser (returns a guarded parser, returns an error when the other parser returns an error).
    fn and_then_try<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::ZipTry> where Self:Sized, P: ParserOf<S> { self.and_then(other).map(impls::ZipTry) }

    /// Sequencing with a parser (returns a guarded parser, returns an error when either parser returns an error).
    fn try_and_then_try<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::TryZipTry> where Self:Sized, P: ParserOf<S> { self.and_then(other).map(impls::TryZipTry) }

    /// Iterate one or more times (returns a guarded parser).
    fn plus<F>(self, factory: F) -> impls::PlusParser<Self,F> where Self:Sized { impls::PlusParser::new(self,factory) }

    /// Iterate zero or more times (returns a parser).
    fn star<F>(self, factory: F) -> impls::StarParser<Self,F> where Self:Sized { impls::StarParser::new(self,factory) }

    /// Apply a function to the result (returns a guarded parser).
    fn map<F>(self, f: F) -> impls::MapParser<Self,F> where Self:Sized, { impls::MapParser::new(self,f) }

    /// Apply a 2-arguent function to the result (returns a guarded parser).
    fn map2<F>(self, f: F) -> impls::MapParser<Self,impls::Function2<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function2::new(f)) }

    /// Apply a 3-arguent function to the result (returns a guarded parser).
    fn map3<F>(self, f: F) -> impls::MapParser<Self,impls::Function3<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function3::new(f)) }

    /// Apply a 4-arguent function to the result (returns a guarded parser).
    fn map4<F>(self, f: F) -> impls::MapParser<Self,impls::Function4<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function4::new(f)) }

    /// Apply a 5-arguent function to the result (returns a guarded parser).
    fn map5<F>(self, f: F) -> impls::MapParser<Self,impls::Function5<F>> where Self:Sized, { impls::MapParser::new(self,impls::Function5::new(f)) }

    /// Apply a function to the result (returns a guarded parser, returns an error when this parser returns an error).
    fn try_map<F>(self, f: F) -> impls::MapParser<Self,impls::Try<F>> where Self:Sized, { self.map(impls::Try::new(f)) }

    /// Apply a 2-argument function to the result (returns a guarded parser, returns an error when this parser returns an error).
    fn try_map2<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function2<F>>> where Self:Sized, { self.try_map(impls::Function2::new(f)) }

    /// Apply a 3-argument function to the result (returns a guarded parser, returns an error when this parser returns an error).
    fn try_map3<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function3<F>>> where Self:Sized, { self.try_map(impls::Function3::new(f)) }

    /// Apply a 4-argument function to the result (returns a guarded parser, returns an error when this parser returns an error).
    fn try_map4<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function4<F>>> where Self:Sized, { self.try_map(impls::Function4::new(f)) }

    /// Apply a 5-argument function to the result (returns a guarded parser, returns an error when this parser returns an error).
    fn try_map5<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function5<F>>> where Self:Sized, { self.try_map(impls::Function5::new(f)) }

    /// Replace the result with the input.
    ///
    /// This does its best to avoid having to buffer the input. The result of a buffered parser
    /// may be borrowed (because no buffering was required) or owned (because buffering was required).
    /// Buffering is required in the case that the input was provided in chunks, rather than
    /// contiguously. For example:
    ///
    /// ```
    /// # use parsimonious::{character_guard,ignore,GuardedParserOf,StatefulParserOf};
    /// # use parsimonious::GuardedParseResult::{Commit};
    /// # use parsimonious::ParseResult::{Done,Continue};
    /// # use parsimonious::Str::{Borrowed,Owned};
    /// let parser = character_guard(char::is_alphabetic).plus(ignore).buffer();
    /// match parser.parse("abc!") {
    ///     Commit(Done("!",result)) => assert_eq!(result,Borrowed("abc")),
    ///     _ => panic!("can't happen"),
    /// }
    /// match parser.parse("abc") {
    ///     Commit(Continue(parsing)) => match parsing.parse("def!") {
    ///         Done("!",result) => assert_eq!(result,Owned(String::from("abcdef"))),
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```
    fn buffer(self) -> impls::BufferedGuardedParser<Self> where Self:Sized, { impls::BufferedGuardedParser::new(self) }

}

/// The result of a guarded parse.
pub enum GuardedParseResult<P,S> where P: StatefulParserOf<S> {
    /// The input was empty.
    Empty,
    /// The parser must backtrack.
    Abort(S),
    /// The parser has committed to parsing the input.
    Commit(ParseResult<P,S>),
}

impl<P,S> GuardedParseResult<P,S> where P: StatefulParserOf<S> {
    /// Apply a function the the Commit branch of a guarded parse result
    pub fn map<F,Q>(self, f: F) -> GuardedParseResult<Q,S> where Q: StatefulParserOf<S,Output=P::Output>, F: Function<P,Output=Q> {
        match self {
            Empty => Empty,
            Abort(s) => Abort(s),
            Commit(c) => Commit(c.map(f)),
        }
    }
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
/// type is `Box<StatefulParserOf<S,Output=T>`. There are two issues with this...
///
/// Firstly, the lifetimes mentioned in the type of the parser may change over time.
/// For example, the program:
///
/// ```text
/// fn check_results (self, rest: &'b str, result: String) {
///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
/// }
/// let parser = character_guard(char::is_alphanumeric).star(String::new);
/// let stateful = parser.init();
/// let boxed: Box<StatefulParserOf<&'a str,Output=String>> = Box::new(stateful);
/// let stuff: &'b str = "abc123!";
/// match boxed.parse(stuff) {
///    Done(rest,result) => self.check_results(rest,result),
///    _ => println!("can't happen"),
/// }
/// ```
///
/// does not typecheck, because the type of `boxed` is fixed as containing parsers for input `&'a str`,
/// but it was fed input of type `&'b str`. To fix this, we change the type of the box to be
/// polymorphic in the lifetime of the parser:
///
/// ```text
/// fn check_results (self, rest: &'b str, result: String) {
///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
/// }
/// let parser = character_guard(char::is_alphanumeric).star(String::new);
/// let stateful = parser.init();
/// let boxed: Box<for <'a> StatefulParserOf<&'a str,Output=String>> = Box::new(stateful);
/// let stuff: &'b str = "abc123!";
/// match boxed.parse(stuff) {
///    Done(rest,result) => self.check_results(rest,result),
///    _ => println!("can't happen"),
/// }
/// ```
///
/// Secondly, the `StatefulParserOf` trait is not
/// [object-safe](https://doc.rust-lang.org/book/trait-objects.html#object-safety),
/// so cannot be boxed and unboxed safely. In order to address this, there is a trait
/// `BoxableParserOf<S,Output=T>`, which represents stateful parsers, but is object-safe
/// and so can be boxed and unboxed safely:
///
/// ```
/// # struct Foo<'a>(&'a str);
/// # impl<'b> Foo<'b> {
/// fn check_results (self, rest: &'b str, result: String) {
///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
/// }
/// # fn foo(self) {
/// # use parsimonious::{character_guard,ignore,GuardedParserOf,ParserOf,BoxableParserOf,StatefulParserOf};
/// # use parsimonious::ParseResult::{Done,Continue};
/// let parser = character_guard(char::is_alphanumeric).star(String::new);
/// let stateful = parser.init();
/// let boxed: Box<for <'a> BoxableParserOf<&'a str,Output=String>> = Box::new(stateful.boxable());
/// let stuff: &'b str = "abc123!";
/// match boxed.parse(stuff) {
///    Done(rest,result) => self.check_results(rest,result),
///    _ => println!("can't happen"),
/// }
/// # } }
/// ```
///
/// The type `Box<BoxableParserOf<S,Output=T>>` implements the trait
/// `StatefulParserOf<S,Output=T>`, so boxes can be used as parsers,
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
/// fn mk_tree(_: char, children: Vec<Tree>, _: Option<char>) -> Tree {
///     Tree(children)
/// }
/// let LPAREN = character_guard(is_lparen);
/// let RPAREN = character(is_rparen);
/// let TREE = LPAREN
///     .and_then(TREE.star(Vec::new))
///     .and_then(RPAREN)
///     .map3(mk_tree);
/// ```
///
/// but this doesn't work because it gives the definition of `TREE` in terms of itself,
/// and Rust doesn't allow this kind of cycle.
///
/// Instead, the solution is to define a struct `TreeParser`, and then implement `GuardedParserOf<&str>`
/// for it. The type of the state of a `TreeParser` is a box containing an appropriate
/// `BoxableParserState` trait:
///
/// ```
/// # use parsimonious::{BoxableParserOf};
/// # struct Tree(Vec<Tree>);
/// type TreeParserState = Box<for<'b> BoxableParserOf<&'b str, Output=Tree>>;
/// ```
///
/// The implementation of `GuardedParserOf<&str>` for `TreeParser` is mostly straightfoward:
///
/// ```
/// # use parsimonious::{character,character_guard,GuardedParserOf,ParserOf,BoxableParserOf,StatefulParserOf,GuardedParseResult};
/// # use parsimonious::ParseResult::{Done,Continue};
/// # use parsimonious::GuardedParseResult::{Commit};
/// # #[derive(Eq,PartialEq,Clone,Debug)]
/// struct Tree(Vec<Tree>);
/// # #[derive(Copy,Clone,Debug)]
/// struct TreeParser;
/// let TREE = TreeParser;
/// type TreeParserState = Box<for<'b> BoxableParserOf<&'b str, Output=Tree>>;
/// impl<'a> GuardedParserOf<&'a str> for TreeParser {
///     type Output = Tree;
///     type State = TreeParserState;
///     fn parse(&self, data: &'a str) -> GuardedParseResult<Self::State,&'a str> {
///         // ... parser goes here...`
/// #       fn is_lparen(ch: char) -> bool { ch == '(' }
/// #       fn is_rparen(ch: char) -> bool { ch == ')' }
/// #       fn mk_tree(_: char, children: Vec<Tree>, _: Option<char>) -> Tree { Tree(children) }
/// #       fn mk_box<P>(parser: P) -> TreeParserState where P: 'static+for<'a> StatefulParserOf<&'a str, Output=Tree> { Box::new(parser.boxable())  }
/// #       let LPAREN = character_guard(is_lparen);
/// #       let RPAREN = character(is_rparen);
/// #       let parser = LPAREN.and_then(TreeParser.star(Vec::new)).and_then(RPAREN).map3(mk_tree);
/// #       parser.parse(data).map(mk_box)
///     }
/// }
/// ```
///
/// The important thing is that the definiton of `parse` can make use of `TREE`, so the parser can call itself
/// recursively, then box up the result state:
///
/// ```
/// # use parsimonious::{character,character_guard,GuardedParserOf,ParserOf,BoxableParserOf,StatefulParserOf,GuardedParseResult};
/// # use parsimonious::ParseResult::{Done,Continue};
/// # use parsimonious::GuardedParseResult::{Commit};
/// # #[derive(Eq,PartialEq,Clone,Debug)]
/// struct Tree(Vec<Tree>);
/// # #[derive(Copy,Clone,Debug)]
/// struct TreeParser;
/// type TreeParserState = Box<for<'b> BoxableParserOf<&'b str, Output=Tree>>;
/// impl<'a> GuardedParserOf<&'a str> for TreeParser {
///     type Output = Tree;
///     type State = TreeParserState;
///     fn parse(&self, data: &'a str) -> GuardedParseResult<Self::State,&'a str> {
///         fn is_lparen(ch: char) -> bool { ch == '(' }
///         fn is_rparen(ch: char) -> bool { ch == ')' }
///         fn mk_tree(_: char, children: Vec<Tree>, _: Option<char>) -> Tree {
///             Tree(children)
///         }
///         fn mk_box<P>(parser: P) -> TreeParserState
///         where P: 'static+for<'a> StatefulParserOf<&'a str, Output=Tree> {
///             Box::new(parser.boxable())
///         }
///         let LPAREN = character_guard(is_lparen);
///         let RPAREN = character(is_rparen);
///         let parser = LPAREN
///             .and_then(TreeParser.star(Vec::new))
///             .and_then(RPAREN)
///             .map3(mk_tree);
///         parser.parse(data).map(mk_box)
///     }
/// }
/// let TREE = TreeParser;
/// match TREE.parse("((") {
///     Commit(Continue(parsing)) => match parsing.parse(")()))") {
///         Done(")",result) => assert_eq!(result,Tree(vec![Tree(vec![]),Tree(vec![])])),
///          _ => panic!("can't happen"),
///     },
///     _ => panic!("can't happen"),
/// }
/// ```
///
/// The reason for making `BoxableParserOf<S>` a different trait from `StatefulParserOf<S>`
/// is that it provides weaker safety guarantees. `StatefulParserOf<S>` enforces that
/// clients cannot call `parse` after `done`, but `BoxableParserOf<S>` does not.

pub trait BoxableParserOf<S> {
    type Output;
    fn parse_boxable(&mut self, value: S) -> Option<(S,Self::Output)>;
    fn done_boxable(&mut self) -> Self::Output;
}

/// A trait for one-argument functions.
///
/// This trait is just the same as `Fn(T) -> U`, but can be implemented by a struct.
/// This is useful, as it allows the function type to be named, for example
///
/// ```
/// # use parsimonious::{Function,character};
/// # use parsimonious::impls::{CharacterParser};
/// struct AlphaNumeric;
/// impl Function<char> for AlphaNumeric {
///     type Output = bool;
///     fn apply(&self, arg: char) -> bool { arg.is_alphanumeric() }
/// }
/// let parser: CharacterParser<AlphaNumeric> =
///     character(AlphaNumeric);
/// ```
///
/// Here, we can name the type of the parser `CharacterParser<AlphaNumeric>`,
/// which would not be possible if `character` took its argument as a `Fn(T) -> U`,
/// since `typeof` is not implemented in Rust.
/// At some point, Rust will probably get abstract return types,
/// at which point the main need for this type will go away.

pub trait Function<T> {
    type Output;
    fn apply(&self, arg: T) -> Self::Output;
}

impl<F,S,T> Function<S> for F where F: Fn(S) -> T {
    type Output = T;
    fn apply(&self, arg: S) -> T { self(arg) }
}

/// A trait for factories.

pub trait Factory {
    type Output;
    fn build(&self) -> Self::Output;
}

impl<F,T> Factory for F where F: Fn() -> T {
    type Output = T;
    fn build(&self) -> T { self() }
}

/// A trait for consumers of data, typically buffers.
///
/// # Examples
///
/// `String` is a consumer of `&str` and of `char`.
///
/// ```
/// # use parsimonious::Consumer;
/// let mut buffer = String::new();
/// buffer.accept("abc");
/// buffer.accept('d');
/// assert_eq!(buffer,"abcd");
/// ```
///
/// `Vec<T>` is a consumer of `&[T]` when `T` is `Clone`, and of `T`.
///
/// ```
/// # use parsimonious::Consumer;
/// let mut buffer = Vec::new();
/// buffer.accept(&[1,2,3][..]);
/// buffer.accept(4);
/// assert_eq!(buffer,&[1,2,3,4]);
/// ```
///
/// The unit type `()` is a trivial consumer that discards data.
///
/// ```
/// # use parsimonious::Consumer;
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

pub fn ignore() -> () { () }

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
    fn accept(&mut self, x: char) { self.push(x); }
}

impl<'a,T> Consumer<&'a[T]> for Vec<T> where T: Clone {
    fn accept(&mut self, arg: &'a[T]) {
        self.extend(arg.iter().cloned());
    }
}

impl<T> Consumer<T> for Vec<T> {
    fn accept(&mut self, x: T) { self.push(x); }
}

impl<C,T,E> Consumer<Result<T,E>> for Result<C,E> where C: Consumer<T> {
    fn accept(&mut self, value: Result<T,E>) {
        let err = match *self {
            Err(_) => return,
            Ok(ref mut consumer) => match value {
                Err(err) => err,
                Ok(value) => return consumer.accept(value),
            },
        };
        *self = Err(err);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Str<'a> {
    Borrowed(&'a str),
    Owned(String),
}

pub fn character<F>(f: F) -> impls::CharacterParser<F> where F: Function<char,Output=bool> {
    impls::CharacterParser::new(f)
}

pub fn character_guard<F>(f: F) -> impls::CharacterGuardedParser<F> where F: Function<char,Output=bool> {
    impls::CharacterGuardedParser::new(f)
}

pub mod impls {

    //! Provide implementations of parser traits.

    use super::{StatefulParserOf,GuardedParserOf,ParserOf,BoxableParserOf,ParseResult,GuardedParseResult,Factory,Function,Consumer,Str};
    use super::ParseResult::{Continue,Done};
    use super::GuardedParseResult::{Abort,Commit,Empty};
    use super::Str::{Borrowed,Owned};

    use self::AndThenStatefulParser::{InLhs,InRhs};
    use self::OrElseStatefulParser::{Lhs,Rhs};
    use self::OrEmitStatefulParser::{Unresolved,Resolved};

    // ----------- N-argument functions ---------------

    #[derive(Copy, Clone, Debug)]
    pub struct Function2<F>(F);

    impl<F> Function2<F> {
        pub fn new(f: F) -> Self { Function2(f) }
    }

    impl<F,S1,S2,T> Function<(S1,S2)> for Function2<F> where F: Fn(S1,S2) -> T {
        type Output = T;
        fn apply(&self, args: (S1,S2)) -> T {
            (self.0)(args.0,args.1)
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct Function3<F>(F);

    impl<F> Function3<F> {
        pub fn new(f: F) -> Self { Function3(f) }
    }

    impl<F,S1,S2,S3,T> Function<((S1,S2),S3)> for Function3<F> where F: Fn(S1,S2,S3) -> T {
        type Output = T;
        fn apply(&self, args: ((S1,S2),S3)) -> T {
            (self.0)((args.0).0,(args.0).1,args.1)
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct Function4<F>(F);

    impl<F> Function4<F> {
        pub fn new(f: F) -> Self { Function4(f) }
    }

    impl<F,S1,S2,S3,S4,T> Function<(((S1,S2),S3),S4)> for Function4<F> where F: Fn(S1,S2,S3,S4) -> T {
        type Output = T;
        fn apply(&self, args: (((S1,S2),S3),S4)) -> T {
            (self.0)(((args.0).0).0,((args.0).0).1,(args.0).1,args.1)
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct Function5<F>(F);

    impl<F> Function5<F> {
        pub fn new(f: F) -> Self { Function5(f) }
    }

    impl<F,S1,S2,S3,S4,S5,T> Function<((((S1,S2),S3),S4),S5)> for Function5<F> where F: Fn(S1,S2,S3,S4,S5) -> T {
        type Output = T;
        fn apply(&self, args: ((((S1,S2),S3),S4),S5)) -> T {
            (self.0)((((args.0).0).0).0,(((args.0).0).0).1,((args.0).0).1,(args.0).1,args.1)
        }
    }

    // ----------- Deal with errors ---------------

    #[derive(Copy, Clone, Debug)]
    pub struct Try<F>(F);
    impl<F,S,T,E> Function<Result<S,E>> for Try<F> where F: Function<S,Output=Result<T,E>> {
        type Output = Result<T,E>;
        fn apply(&self, args: Result<S,E>) -> Result<T,E> { self.0.apply(try!(args)) }
    }
    impl<F> Try<F> {
        pub fn new(f: F) -> Try<F> { Try(f) }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct TryZip;
    impl<S,T,E> Function<(Result<S,E>,T)> for TryZip {
        type Output = Result<(S,T),E>;
        fn apply(&self, args: (Result<S,E>,T)) -> Result<(S,T),E> { Ok((try!(args.0),args.1)) }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct ZipTry;
    impl<S,T,E> Function<(S,Result<T,E>)> for ZipTry {
        type Output = Result<(S,T),E>;
        fn apply(&self, args: (S,Result<T,E>)) -> Result<(S,T),E> { Ok((args.0,try!(args.1))) }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct TryZipTry;
    impl<S,T,E> Function<(Result<S,E>,Result<T,E>)> for TryZipTry {
        type Output = Result<(S,T),E>;
        fn apply(&self, args: (Result<S,E>,Result<T,E>)) -> Result<(S,T),E> { Ok((try!(args.0),try!(args.1))) }
    }

   // ----------- Map ---------------

    #[derive(Debug)]
    pub struct MapStatefulParser<P,F>(P,F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<P,F> Copy for MapStatefulParser<P,F> where P: Copy, F: Copy {}
    impl<P,F> Clone for MapStatefulParser<P,F> where P: Clone, F: Copy {
        fn clone(&self) -> Self {
            MapStatefulParser(self.0.clone(),self.1)
        }
    }

    // NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
    // See https://github.com/rust-lang/rust/issues/30867 for more details.
    impl<P,F,S,T> StatefulParserOf<S> for MapStatefulParser<P,F> where P: StatefulParserOf<S,Output=T>, F: Function<T> {
        type Output = F::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self.0.parse(value) {
                Done(rest,result) => Done(rest,self.1.apply(result)),
                Continue(parsing) => Continue(MapStatefulParser(parsing,self.1)),
            }
        }
        fn done(self) -> Self::Output {
            self.1.apply(self.0.done())
        }
    }

    #[derive(Debug)]
    pub struct MapParser<P,F>(P,F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<P,F> Copy for MapParser<P,F> where P: Copy, F: Copy {}
    impl<P,F> Clone for MapParser<P,F> where P: Clone, F: Copy {
        fn clone(&self) -> Self {
            MapParser(self.0.clone(),self.1)
        }
    }

    impl<P,F,S> GuardedParserOf<S> for MapParser<P,F> where P: GuardedParserOf<S>, F: Copy+Function<P::Output> {
        type Output = F::Output;
        type State = MapStatefulParser<P::State,F>;
        fn parse(&self, value: S) -> GuardedParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty => Empty,
                Commit(Done(rest,result)) => Commit(Done(rest,self.1.apply(result))),
                Commit(Continue(parsing)) => Commit(Continue(MapStatefulParser(parsing,self.1))),
                Abort(value) => Abort(value),
            }
        }
    }

    impl<P,F,S> ParserOf<S> for MapParser<P,F> where P: ParserOf<S>, F: Copy+Function<P::Output> {
        type Output = F::Output;
        type State = MapStatefulParser<P::State,F>;
        fn init(&self) -> Self::State {
            MapStatefulParser(self.0.init(),self.1)
        }
    }

    impl<P,F> MapParser<P,F> {
        pub fn new(parser: P, function: F) -> Self {
            MapParser(parser,function)
        }
    }

    // ----------- Sequencing ---------------

    #[derive(Copy, Clone, Debug)]
    pub struct AndThenParser<P,Q>(P,Q);

    impl<P,Q,S> ParserOf<S> for AndThenParser<P,Q> where P: ParserOf<S>, Q: ParserOf<S> {
        type Output = (P::Output,Q::Output);
        type State = AndThenStatefulParser<P::State,Q::State,P::Output>;
        fn init(&self) -> Self::State {
            InLhs(self.0.init(),self.1.init())
        }
    }

    impl<P,Q,S> GuardedParserOf<S> for AndThenParser<P,Q> where P: GuardedParserOf<S>, Q: ParserOf<S> {
        type Output = (P::Output,Q::Output);
        type State = AndThenStatefulParser<P::State,Q::State,P::Output>;
        fn parse(&self, value: S) -> GuardedParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty => Empty,
                Commit(Done(rest,result1)) => match self.1.init().parse(rest) {
                    Done(rest,result2) => Commit(Done(rest,(result1,result2))),
                    Continue(parsing) => Commit(Continue(InRhs(result1,parsing))),
                },
                Commit(Continue(parsing)) => Commit(Continue(InLhs(parsing,self.1.init()))),
                Abort(value) => Abort(value),
            }
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub enum AndThenStatefulParser<P,Q,T> {
        InLhs(P,Q),
        InRhs(T,Q),
    }

    impl<P,Q,S> StatefulParserOf<S> for AndThenStatefulParser<P,Q,P::Output> where P: StatefulParserOf<S>, Q: StatefulParserOf<S> {
        type Output = (P::Output,Q::Output);
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                InLhs(lhs,rhs) => {
                    match lhs.parse(value) {
                        Done(rest,result1) => match rhs.parse(rest) {
                            Done(rest,result2) => Done(rest,(result1,result2)),
                            Continue(parsing) => Continue(InRhs(result1,parsing)),
                        },
                        Continue(parsing) => Continue(InLhs(parsing,rhs)),
                    }
                },
                InRhs(result1,rhs) => {
                    match rhs.parse(value) {
                        Done(rest,result2) => Done(rest,(result1,result2)),
                        Continue(parsing) => Continue(InRhs(result1,parsing)),
                    }
                },
            }
        }
        fn done(self) -> Self::Output {
            match self {
                InLhs(lhs,rhs) => (lhs.done(), rhs.done()),
                InRhs(result1,rhs) => (result1, rhs.done()),
            }
        }
    }

    impl<P,Q> AndThenParser<P,Q> {
        pub fn new(lhs: P, rhs: Q) -> Self {
            AndThenParser(lhs,rhs)
        }
    }

    // ----------- Choice ---------------

    #[derive(Copy, Clone, Debug)]
    pub struct OrElseGuardedParser<P,Q>(P,Q);

    impl<P,Q,S> GuardedParserOf<S> for OrElseGuardedParser<P,Q> where P: GuardedParserOf<S>, Q: GuardedParserOf<S,Output=P::Output> {
        type Output = P::Output;
        type State = OrElseStatefulParser<P::State,Q::State>;
        fn parse(&self, value: S) -> GuardedParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty => Empty,
                Commit(Done(rest,result)) => Commit(Done(rest,result)),
                Commit(Continue(parsing)) => Commit(Continue(Lhs(parsing))),
                Abort(value) => match self.1.parse(value) {
                    Empty => Empty,
                    Commit(Done(rest,result)) => Commit(Done(rest,result)),
                    Commit(Continue(parsing)) => Commit(Continue(Rhs(parsing))),
                    Abort(value) => Abort(value),
                }
            }
        }
    }

    impl<P,Q> OrElseGuardedParser<P,Q> {
        pub fn new(lhs: P, rhs: Q) -> Self {
            OrElseGuardedParser(lhs,rhs)
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub enum OrElseStatefulParser<P,Q> {
        Lhs(P),
        Rhs(Q),
    }

    impl<P,Q,S> StatefulParserOf<S> for OrElseStatefulParser<P,Q> where P: StatefulParserOf<S>, Q: StatefulParserOf<S,Output=P::Output> {
        type Output = P::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                Lhs(lhs) => {
                    match lhs.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(parsing) => Continue(Lhs(parsing)),
                    }
                },
                Rhs(rhs) => {
                    match rhs.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(parsing) => Continue(Rhs(parsing)),
                    }
                },
            }
        }
        fn done(self) -> Self::Output {
            match self {
                Lhs(lhs) => lhs.done(),
                Rhs(rhs) => rhs.done(),
            }
        }
    }

    #[derive(Debug)]
    pub enum OrEmitStatefulParser<P,F,R> {
        Unresolved(P,F),
        Resolved(R),
    }

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<P,F,R> Copy for OrEmitStatefulParser<P,F,R> where P: Copy, F: Copy, R: Copy {}
    impl<P,F,R> Clone for OrEmitStatefulParser<P,F,R> where P: Copy, F: Copy, R: Clone {
        fn clone(&self) -> Self {
            match *self {
                Unresolved(parser,default) => Unresolved(parser,default),
                Resolved(ref parser) => Resolved(parser.clone()),
            }
        }
    }

    impl<P,F,S> StatefulParserOf<S> for OrEmitStatefulParser<P,F,P::State> where P: GuardedParserOf<S>, F: Factory<Output=P::Output> {
        type Output = P::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                Unresolved(parser,default) => {
                    match parser.parse(value) {
                        Empty => Continue(Unresolved(parser,default)),
                        Commit(Done(rest,result)) => Done(rest,result),
                        Commit(Continue(parsing)) => Continue(Resolved(parsing)),
                        Abort(value) => Done(value,default.build()),
                    }
                },
                Resolved(parser) => {
                    match parser.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(parsing) => Continue(Resolved(parsing)),
                    }
                }
            }
        }
        fn done(self) -> Self::Output {
            match self {
                Unresolved(_,default) => default.build(),
                Resolved(parser) => parser.done(),
            }
        }
    }

    pub struct OrEmitParser<P,F>(P,F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<P,F> Copy for OrEmitParser<P,F> where P: Copy, F: Copy {}
    impl<P,F> Clone for OrEmitParser<P,F> where P: Clone, F: Copy {
        fn clone(&self) -> Self {
            OrEmitParser(self.0.clone(),self.1)
        }
    }

    impl<P,F,S> ParserOf<S> for OrEmitParser<P,F> where P: Clone+GuardedParserOf<S>, F: Copy+Factory<Output=P::Output> {
        type Output = P::Output;
        type State = OrEmitStatefulParser<P,F,P::State>;
        fn init(&self) -> Self::State {
            Unresolved(self.0.clone(),self.1)
        }
    }

    impl<P,F> OrEmitParser<P,F> {
        pub fn new(parser: P, default: F) -> Self {
            OrEmitParser(parser, default)
        }
    }

    // ----------- Kleene star ---------------

    #[derive(Clone,Debug)]
    pub struct StarStatefulParser<P,Q,T>(P,Option<Q>,T);

    impl<P,T,S> StatefulParserOf<S> for StarStatefulParser<P,P::State,T> where P: Copy+GuardedParserOf<S>, T: Consumer<P::Output> {
        type Output = T;
        fn parse(mut self, mut value: S) -> ParseResult<Self,S> {
            loop {
                match self.1.take() {
                    None => match self.0.parse(value) {
                        Empty => return Continue(StarStatefulParser(self.0,None,self.2)),
                        Commit(Continue(parsing)) => return Continue(StarStatefulParser(self.0,Some(parsing),self.2)),
                        Commit(Done(rest,result)) => { self.2.accept(result); value = rest; },
                        Abort(rest) => return Done(rest,self.2),
                    },
                    Some(parser) => match parser.parse(value) {
                        Continue(parsing) => return Continue(StarStatefulParser(self.0,Some(parsing),self.2)),
                        Done(rest,result) => { self.2.accept(result); value = rest; },
                    }
                }
            }
        }
        fn done(self) -> T {
            self.2
        }
    }

    #[derive(Debug)]
    pub struct PlusParser<P,F>(P,F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<P,F> Copy for PlusParser<P,F> where P: Copy, F: Copy {}
    impl<P,F> Clone for PlusParser<P,F> where P: Clone, F: Copy {
        fn clone(&self) -> Self {
            PlusParser(self.0.clone(),self.1)
        }
    }

    impl<P,F,S> GuardedParserOf<S> for PlusParser<P,F> where P: Copy+GuardedParserOf<S>, F: Factory, F::Output: Consumer<P::Output> {
        type Output = F::Output;
        type State = StarStatefulParser<P,P::State,F::Output>;
        fn parse(&self, value: S) -> GuardedParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty => Empty,
                Abort(rest) => Abort(rest),
                Commit(Continue(parsing)) => Commit(Continue(StarStatefulParser(self.0,Some(parsing),self.1.build()))),
                Commit(Done(rest,result)) => {
                    let mut buffer = self.1.build();
                    buffer.accept(result);
                    Commit(StarStatefulParser(self.0,None,buffer).parse(rest))
                }
            }
        }
    }

    impl<P,F> PlusParser<P,F> {
        pub fn new(parser: P, factory: F) -> Self {
            PlusParser(parser,factory)
        }
    }

    #[derive(Debug)]
    pub struct StarParser<P,F>(P,F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<P,F> Copy for StarParser<P,F> where P: Copy, F: Copy {}
    impl<P,F> Clone for StarParser<P,F> where P: Clone, F: Copy {
        fn clone(&self) -> Self {
            StarParser(self.0.clone(),self.1)
        }
    }

    impl<P,F,S> ParserOf<S> for StarParser<P,F> where P: Copy+GuardedParserOf<S>, F: Factory, F::Output: Consumer<P::Output> {
        type Output = F::Output;
        type State = StarStatefulParser<P,P::State,F::Output>;
        fn init(&self) -> Self::State {
            StarStatefulParser(self.0,None,self.1.build())
        }
    }

    impl<P,F> StarParser<P,F> {
        pub fn new(parser: P, factory: F) -> Self {
            StarParser(parser,factory)
        }
    }

    // ----------- Constant parsers -------------

    #[derive(Copy, Clone, Debug)]
    enum Impossible{}

    impl Impossible {
        fn cant_happen<T>(&self) -> T {
            match *self {}
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct ImpossibleStatefulParser<T>(Impossible,T);

    impl<T,S> StatefulParserOf<S> for ImpossibleStatefulParser<T> {
        type Output = T;
        fn parse(self, _: S) -> ParseResult<Self,S> {
            self.0.cant_happen()
        }
        fn done(self) -> T {
            self.0.cant_happen()
        }
    }

    #[derive(Debug)]
    pub struct CharacterStatefulParser<F>(F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<F> Copy for CharacterStatefulParser<F> where F: Copy {}
    impl<F> Clone for CharacterStatefulParser<F> where F: Copy {
        fn clone(&self) -> Self {
            CharacterStatefulParser(self.0)
        }
    }

    impl<'a,F> StatefulParserOf<&'a str> for CharacterStatefulParser<F> where F: Function<char,Output=bool> {
        type Output = Option<char>;
        fn parse(self, value: &'a str) -> ParseResult<Self,&'a str> {
            match value.chars().next() {
                None => Continue(self),
                Some(ch) if self.0.apply(ch) => {
                    let len = ch.len_utf8();
                    Done(&value[len..],Some(ch))
                },
                Some(_) => Done(value,None)
            }
        }
        fn done(self) -> Option<char> {
            None
        }
    }

    #[derive(Debug)]
    pub struct CharacterParser<F>(F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<F> Copy for CharacterParser<F> where F: Copy {}
    impl<F> Clone for CharacterParser<F> where F: Copy {
        fn clone(&self) -> Self {
            CharacterParser(self.0)
        }
    }

    impl<'a,F> ParserOf<&'a str> for CharacterParser<F> where F: Copy+Function<char,Output=bool> {
        type Output = Option<char>;
        type State = CharacterStatefulParser<F>;
        fn init(&self) -> Self::State {
            CharacterStatefulParser(self.0)
        }
    }

    impl<F> CharacterParser<F> {
        pub fn new(function: F) -> Self {
            CharacterParser(function)
        }
    }

    #[derive(Debug)]
    pub struct CharacterGuardedParser<F>(F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<F> Copy for CharacterGuardedParser<F> where F: Copy {}
    impl<F> Clone for CharacterGuardedParser<F> where F: Copy {
        fn clone(&self) -> Self {
            CharacterGuardedParser(self.0)
        }
    }

    impl<'a,F> GuardedParserOf<&'a str> for CharacterGuardedParser<F> where F: Function<char,Output=bool> {
        type Output = char;
        type State = ImpossibleStatefulParser<char>;
        fn parse(&self, value: &'a str) -> GuardedParseResult<Self::State,&'a str> {
            match value.chars().next() {
                None => Empty,
                Some(ch) if self.0.apply(ch) => {
                    let len = ch.len_utf8();
                    Commit(Done(&value[len..],ch))
                },
                Some(_) => Abort(value),
            }
        }
    }

    impl<F> CharacterGuardedParser<F> {
        pub fn new(function: F) -> Self {
            CharacterGuardedParser(function)
        }
    }

    // ----------- Buffering -------------

    // If m is a GuardedParserOf<&'a str>, then
    // m.buffer() is a GuardedParserOf<&'a str> with Output Str<'a>.
    // It does as little buffering as it can, but it does allocate as buffer for the case
    // where the boundary marker of the input is misaligned with that of the parser.
    // For example, m is matching string literals, and the input is '"abc' followed by 'def"'
    // we have to buffer up '"abc'.

    // TODO(ajeffrey): make this code generic in its input
    // this may involove something like:
    //
    // pub trait IntoOwned {
    //     type Owned;
    //     fn into_owned(self) -> Self::Owned;
    // }
    //
    // impl<'a,T> IntoOwned for &'a T where T: ToOwned {
    //     type Owned = T::Owned;
    //     fn into_owned(self) -> T::Owned { self.to_owned() }
    // }

    #[derive(Copy, Clone, Debug)]
    pub struct BufferedGuardedParser<P>(P);

    impl<'a,P> GuardedParserOf<&'a str> for BufferedGuardedParser<P> where P: GuardedParserOf<&'a str> {
        type Output = Str<'a>;
        type State = BufferedStatefulParser<P::State>;
        fn parse(&self, value: &'a str) -> GuardedParseResult<Self::State,&'a str> {
            match self.0.parse(value) {
                Empty => Empty,
                Commit(Done(rest,_)) => Commit(Done(rest,Borrowed(&value[..(value.len() - rest.len())]))),
                Commit(Continue(parsing)) => Commit(Continue(BufferedStatefulParser(parsing,String::from(value)))),
                Abort(value) => Abort(value),
            }
        }
    }

    impl<P> BufferedGuardedParser<P> {
        pub fn new(parser: P) -> Self {
            BufferedGuardedParser(parser)
        }
    }

    #[derive(Clone,Debug)]
    pub struct BufferedStatefulParser<P>(P,String);

    impl<'a,P> StatefulParserOf<&'a str> for BufferedStatefulParser<P> where P: StatefulParserOf<&'a str> {
        type Output = Str<'a>;
        fn parse(mut self, value: &'a str) -> ParseResult<Self,&'a str> {
            match self.0.parse(value) {
                Done(rest,_) => { self.1.push_str(&value[..(value.len() - rest.len())]); Done(rest,Owned(self.1)) },
                Continue(parsing) => { self.1.push_str(value); Continue(BufferedStatefulParser(parsing,self.1)) },
            }
        }
        fn done(self) -> Self::Output {
            Owned(self.1)
        }
    }

    // ----------- Parsers which are boxable -------------

    pub struct BoxableParser<P> (Option<P>);
    impl<P,S> BoxableParserOf<S> for BoxableParser<P> where P: StatefulParserOf<S> {
        type Output = P::Output;
        fn parse_boxable(&mut self, value: S) -> Option<(S,Self::Output)> {
            match self.0.take().unwrap().parse(value) {
                Done(rest,result) => Some((rest,result)),
                Continue(parsing) => { self.0 = Some(parsing); None },
            }
        }
        fn done_boxable(&mut self) -> Self::Output {
            self.0.take().unwrap().done()
        }
    }

    impl<P:?Sized,S> StatefulParserOf<S> for Box<P> where P: BoxableParserOf<S> {
        type Output = P::Output;
        fn parse(mut self, value: S) -> ParseResult<Self,S> {
            match self.parse_boxable(value) {
                Some((rest,result)) => Done(rest,result),
                None => Continue(self),
            }
        }
        fn done(mut self) -> Self::Output {
            self.done_boxable()
        }
    }

    impl<P> BoxableParser<P> {
        pub fn new(parser: P) -> Self {
            BoxableParser(Some(parser))
        }
    }

}

// ----------- Tests -------------

#[allow(non_snake_case,dead_code)]
impl<P,S> GuardedParseResult<P,S> where P: StatefulParserOf<S> {

    fn unEmpty(self) {
        match self {
            Empty => (),
            _     => panic!("GuardedParseResult is not empty"),
        }
    }

    fn unAbort(self) -> S {
        match self {
            Abort(s) => s,
            _        => panic!("GuardedParseResult is not failure"),
        }
    }

    fn unCommit(self) -> ParseResult<P,S> {
        match self {
            Commit(s) => s,
            _       => panic!("GuardedParseResult is not success"),
        }
    }

}

#[allow(non_snake_case,dead_code)]
impl<P,S> ParseResult<P,S> where P: StatefulParserOf<S> {

    fn unDone(self) -> (S,P::Output) {
        match self {
            Done(s,t) => (s,t),
            _         => panic!("ParseResult is not done"),
        }
    }

    fn unContinue(self) -> P {
        match self {
            Continue(p) => p,
            _           => panic!("ParseResult is not continue"),
        }
    }

}

#[test]
fn test_character() {
    let parser = character(char::is_alphabetic);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("989").unDone(),("989",None));
    assert_eq!(parser.init().parse("abc").unDone(),("bc",Some('a')));
}

#[test]
fn test_character_guard() {
    let parser = character_guard(char::is_alphabetic);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("abc").unCommit().unDone(),("bc",'a'));
}

#[test]
fn test_or_emit() {
    fn mk_x() -> char { 'X' }
    let parser = character_guard(char::is_alphabetic).or_emit(mk_x);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("989").unDone(),("989",'X'));
    assert_eq!(parser.init().parse("abc").unDone(),("bc",'a'));
}

#[test]
fn test_map() {
    fn mk_none<T>() -> Option<T> { None }
    let parser = character_guard(char::is_alphabetic).map(Some).or_emit(mk_none);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("989").unDone(),("989",None));
    assert_eq!(parser.init().parse("abc").unDone(),("bc",Some('a')));
}

#[test]
#[allow(non_snake_case)]
fn test_map2() {
    fn f(ch1: char, ch2: Option<char>) -> Option<(char, char)> {
        ch2.and_then(|ch2| Some((ch1,ch2)))
    }
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHANUMERIC).map2(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Some(('a','b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_map3() {
    fn f(ch1: char, ch2: Option<char>, ch3: Option<char>) -> Option<(char, char, char)> {
        ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1,ch2,ch3))))
    }
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).map3(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("ab!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abcd").unCommit().unDone(),("d",Some(('a','b','c'))));
}

#[test]
#[allow(non_snake_case)]
fn test_map4() {
    fn f(ch1: char, ch2: Option<char>, ch3: Option<char>, ch4: Option<char>) -> Option<(char, char, char, char)> {
        ch4.and_then(|ch4| ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1,ch2,ch3,ch4)))))
    }
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).map4(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("ab!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abc!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abcde").unCommit().unDone(),("e",Some(('a','b','c','d'))));
}

#[test]
#[allow(non_snake_case)]
fn test_map5() {
    fn f(ch1: char, ch2: Option<char>, ch3: Option<char>, ch4: Option<char>, ch5: Option<char>) -> Option<(char, char, char, char, char)> {
        ch5.and_then(|ch5| ch4.and_then(|ch4| ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1,ch2,ch3,ch4,ch5))))))
    }
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).map5(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("ab!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abc!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abcd!!").unCommit().unDone(),("!!",None));
    assert_eq!(parser.parse("abcdef").unCommit().unDone(),("f",Some(('a','b','c','d','e'))));
}

#[test]
#[allow(non_snake_case)]
fn test_and_then() {
    fn mk_none<T>() -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHANUMERIC).map(Some).or_emit(mk_none);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("989").unDone(),("989",None));
    assert_eq!(parser.init().parse("a!").unDone(),("!",Some(('a',None))));
    assert_eq!(parser.init().parse("abc").unDone(),("c",Some(('a',Some('b')))));
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("989").unDone(),("89",(None,Some('9'))));
    assert_eq!(parser.init().parse("a!").unDone(),("!",(Some('a'),None)));
    assert_eq!(parser.init().parse("abc").unDone(),("c",(Some('a'),Some('b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then() {
    fn mk_err<T>() -> Result<T,String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
    let ALPHANUMERIC = character_guard(char::is_alphanumeric).map(mk_ok).or_emit(mk_err);
    let parser = character_guard(char::is_alphabetic).map(mk_ok).try_and_then(ALPHANUMERIC);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",Ok(('a',Err(String::from("oh"))))));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Ok(('a',Ok('b')))));
}

#[test]
#[allow(non_snake_case)]
fn test_and_then_try() {
    fn mk_err<T>() -> Result<T,String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
    let ALPHANUMERIC = character_guard(char::is_alphanumeric).map(mk_ok).or_emit(mk_err);
    let parser = character_guard(char::is_alphabetic).map(mk_ok).and_then_try(ALPHANUMERIC);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",Err(String::from("oh"))));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Ok((Ok('a'),'b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then_try() {
    fn mk_err<T>() -> Result<T,String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
    let ALPHANUMERIC = character_guard(char::is_alphanumeric).map(mk_ok).or_emit(mk_err);
    let parser = character_guard(char::is_alphabetic).map(mk_ok).try_and_then_try(ALPHANUMERIC);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",Err(String::from("oh"))));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Ok(('a','b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_or_else() {
    fn mk_none<T>() -> Option<T> { None }
    let NUMERIC = character(char::is_numeric);
    let ALPHABETIC = character(char::is_alphabetic);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHABETIC).map(Some).
        or_else(character_guard(char::is_numeric).and_then(NUMERIC).map(Some)).
        or_emit(mk_none);
    parser.init().parse("").unContinue();
    parser.init().parse("a").unContinue();
    parser.init().parse("9").unContinue();
    assert_eq!(parser.init().parse("!").unDone(),("!",None));
    assert_eq!(parser.init().parse("a9").unDone(),("9",Some(('a',None))));
    assert_eq!(parser.init().parse("9a").unDone(),("a",Some(('9',None))));
    assert_eq!(parser.init().parse("abc").unDone(),("c",Some(('a',Some('b')))));
    assert_eq!(parser.init().parse("123").unDone(),("3",Some(('1',Some('2')))));
}

#[test]
#[allow(non_snake_case)]
fn test_plus() {
    let parser = character_guard(char::is_alphanumeric).plus(String::new);
    parser.parse("").unEmpty();
    parser.parse("!!!").unAbort();
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",String::from("a")));
    assert_eq!(parser.parse("abc98def!").unCommit().unDone(),("!",String::from("abc98def")));
}

#[test]
#[allow(non_snake_case)]
fn test_star() {
    let parser = character_guard(char::is_alphanumeric).star(String::new);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("!!!").unDone(),("!!!",String::from("")));
    assert_eq!(parser.init().parse("a!").unDone(),("!",String::from("a")));
    assert_eq!(parser.init().parse("abc98def!").unDone(),("!",String::from("abc98def")));
}

#[test]
#[allow(non_snake_case)]
fn test_buffer() {
    let ALPHABETIC = character_guard(char::is_alphabetic);
    let ALPHANUMERIC = character_guard(char::is_alphanumeric);
    let parser = ALPHABETIC.and_then(ALPHANUMERIC.star(ignore)).buffer();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",Str::Borrowed("a")));
    assert_eq!(parser.parse("abc!").unCommit().unDone(),("!",Str::Borrowed("abc")));
    let parsing = parser.parse("a").unCommit().unContinue();
    assert_eq!(parsing.parse("bc!").unDone(),("!",Str::Owned(String::from("abc"))));
}

#[test]
#[allow(non_snake_case)]
fn test_different_lifetimes() {
    fn go<'a,'b,P>(ab: &'a str, cd: &'b str, parser: P) where P: Copy+for<'c> ParserOf<&'c str,Output=Option<(char,Option<char>)>> {
        let _: &'a str = parser.init().parse(ab).unDone().0;
        let _: &'b str = parser.init().parse(cd).unDone().0;
        assert_eq!(parser.init().parse(ab).unDone(),("",Some(('a',Some('b')))));
        assert_eq!(parser.init().parse(cd).unDone(),("",Some(('c',Some('d')))));
    }
    fn mk_none<T>() -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = character_guard(char::is_alphabetic).and_then(ALPHANUMERIC).map(Some).or_emit(mk_none);
    go("ab","cd",parser);
}

#[test]
#[allow(non_snake_case)]
fn test_boxable() {

    #[derive(Clone,Debug,Eq,PartialEq)]
    struct Tree(Vec<Tree>);

    #[derive(Copy,Clone,Debug)]
    struct TreeParser;
    type TreeParserState = Box<for<'b> BoxableParserOf<&'b str, Output=Tree>>;
    impl<'a> GuardedParserOf<&'a str> for TreeParser {
        type Output = Tree;
        type State = TreeParserState;
        fn parse(&self, data: &'a str) -> GuardedParseResult<Self::State,&'a str> {
            fn is_lparen(ch: char) -> bool { ch == '(' }
            fn is_rparen(ch: char) -> bool { ch == ')' }
            fn mk_tree(children: ((char, Vec<Tree>), Option<char>)) -> Tree { Tree((children.0).1) }
            fn mk_box<P>(parser: P) -> TreeParserState where P: 'static+for<'a> StatefulParserOf<&'a str, Output=Tree> { Box::new(parser.boxable())  }
            let LPAREN = character_guard(is_lparen);
            let RPAREN = character(is_rparen);
            let parser = LPAREN.and_then(TreeParser.star(Vec::new)).and_then(RPAREN).map(mk_tree);
            parser.parse(data).map(mk_box)
        }
    }

    assert_eq!(TreeParser.parse("!").unAbort(),"!");
    assert_eq!(TreeParser.parse("()!").unCommit().unDone(),("!",Tree(vec![])));
    assert_eq!(TreeParser.parse("(()))").unCommit().unDone(),(")",Tree(vec![Tree(vec![])])));
    assert_eq!(TreeParser.parse("(").unCommit().unContinue().parse(")!").unDone(),("!",Tree(vec![])));
    assert_eq!(TreeParser.parse("((").unCommit().unContinue().parse(")))").unDone(),(")",Tree(vec![Tree(vec![])])));

}
