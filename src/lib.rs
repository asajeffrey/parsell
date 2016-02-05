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

use self::MaybeParseResult::{Empty,Abort,Commit};
use self::ParseResult::{Done,Continue};

// ----------- Types for parsers ------------

/// A trait for stateful parsers.
///
/// Stateful parsers are typically constructed by calling the `init` method of a stateless parser,
/// for example:
///
/// ```
/// # use parsimonious::{character,Parser,Uncommitted,Committed};
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
/// ```
/// # use parsimonious::{character,CHARACTER,Uncommitted,Parser,Committed,Stateful};
/// # use parsimonious::ParseResult::Done;
/// fn mk_err(_: Option<char>) -> Result<char,String> { Err(String::from("Expecting a digit")) }
/// let DIGIT = character(char::is_numeric).map(Ok).or_else(CHARACTER.map(mk_err));
/// let TWO_DIGITS = DIGIT.try_and_then_try(DIGIT);
/// match TWO_DIGITS.init().parse("123") {
///    Done("3",result) => assert_eq!(result,Ok(('1','2'))),
///    _ => panic!("Can't happen"),
/// }
/// ```

pub trait Stateful<S> {

    /// The type of the data being produced by the parser.
    type Output;

    /// Provides data to the parser.
    ///
    /// If `parser: Stateful<S,Output=T>`, then `parser.parse(data)` either:
    ///
    /// * returns `Done(rest, result)` where `rest: S` is any remaining input,
    ///   and `result: T` is the parsed output, or
    /// * returns `Continue(rest,parsing)` where `parsing: Self` is the new state of the parser.
    ///
    /// For example:
    ///
    /// ```
    /// # use parsimonious::{character,Parser,Uncommitted,Committed,Stateful};
    /// # use parsimonious::ParseResult::{Continue,Done};
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// let stateful = parser.init();
    /// match stateful.parse("abc") {
    ///     Continue("",parsing) => match parsing.parse("def!") {
    ///         Done("!",result) => assert_eq!(result,"abcdef"),
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
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
    /// If `parser: Stateful<S,Output=T>`, then `parser.done()` returns a result of type `T`
    /// for example:
    ///
    /// ```
    /// # use parsimonious::{character,Parser,Uncommitted,Committed,Stateful};
    /// # use parsimonious::ParseResult::{Continue,Done};
    /// let parser = character(char::is_alphabetic).star(String::new);
    /// let stateful = parser.init();
    /// match stateful.parse("abc") {
    ///     Continue("",parsing) => match parsing.parse("def") {
    ///         Continue("",parsing) => assert_eq!(parsing.done(),"abcdef"),
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
pub enum ParseResult<P,S> where P: Stateful<S> {
    /// The parse is finished.
    Done(S,P::Output),
    /// The parse can continue.
    Continue(S,P),
}

impl<P,S> ParseResult<P,S> where P: Stateful<S> {
    /// Apply a function the the `Continue` branch of a parse result.
    pub fn map<F,Q>(self, f: F) -> ParseResult<Q,S> where Q: Stateful<S,Output=P::Output>, F: Function<P,Output=Q> {
        match self {
            Done(rest,result) => Done(rest,result),
            Continue(rest,parsing) => Continue(rest,f.apply(parsing)),
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
    fn or_else<P>(self, other: P) -> impls::OrElseParser<Self,P> where Self:Sized { impls::OrElseParser::new(self,other) }

    /// Sequencing with a committed parser
    fn and_then<P>(self, other: P) -> impls::AndThenParser<Self,P> where Self: Sized { impls::AndThenParser::new(self,other) }

    /// Sequencing with a committed parser (bubble any errors from this parser).
    fn try_and_then<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::TryZip> where Self: Sized { self.and_then(other).map(impls::TryZip) }

    /// Sequencing with a committed parser (bubble any errors from that parser).
    fn and_then_try<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::ZipTry> where Self: Sized { self.and_then(other).map(impls::ZipTry) }

    /// Sequencing with a committed parser (bubble any errors from either parser).
    fn try_and_then_try<P>(self, other: P) -> impls::MapParser<impls::AndThenParser<Self,P>,impls::TryZipTry> where Self: Sized { self.and_then(other).map(impls::TryZipTry) }

    /// Iterate one or more times (returns an uncommitted parser).
    fn plus<F>(self, factory: F) -> impls::PlusParser<Self,F> where Self: Sized { impls::PlusParser::new(self,factory) }

    /// Iterate zero or more times (returns a committed parser).
    fn star<F>(self, factory: F) -> impls::StarParser<Self,F> where Self: Sized { impls::StarParser::new(self,factory) }

    /// Apply a function to the result
    fn map<F>(self, f: F) -> impls::MapParser<Self,F> where Self: Sized { impls::MapParser::new(self,f) }

    /// Apply a 2-arguent function to the result
    fn map2<F>(self, f: F) -> impls::MapParser<Self,impls::Function2<F>> where Self: Sized { impls::MapParser::new(self,impls::Function2::new(f)) }

    /// Apply a 3-arguent function to the result
    fn map3<F>(self, f: F) -> impls::MapParser<Self,impls::Function3<F>> where Self: Sized { impls::MapParser::new(self,impls::Function3::new(f)) }

    /// Apply a 4-arguent function to the result
    fn map4<F>(self, f: F) -> impls::MapParser<Self,impls::Function4<F>> where Self: Sized { impls::MapParser::new(self,impls::Function4::new(f)) }

    /// Apply a 5-arguent function to the result
    fn map5<F>(self, f: F) -> impls::MapParser<Self,impls::Function5<F>> where Self: Sized { impls::MapParser::new(self,impls::Function5::new(f)) }

    /// Apply a function to the result (bubble any errors).
    fn try_map<F>(self, f: F) -> impls::MapParser<Self,impls::Try<F>> where Self: Sized { self.map(impls::Try::new(f)) }

    /// Apply a 2-argument function to the result (bubble any errors).
    fn try_map2<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function2<F>>> where Self: Sized { self.try_map(impls::Function2::new(f)) }

    /// Apply a 3-argument function to the result (bubble any errors).
    fn try_map3<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function3<F>>> where Self: Sized { self.try_map(impls::Function3::new(f)) }

    /// Apply a 4-argument function to the result (bubble any errors).
    fn try_map4<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function4<F>>> where Self: Sized { self.try_map(impls::Function4::new(f)) }

    /// Apply a 5-argument function to the result (bubble any errors).
    fn try_map5<F>(self, f: F) -> impls::MapParser<Self,impls::Try<impls::Function5<F>>> where Self: Sized { self.try_map(impls::Function5::new(f)) }

    /// Take the results of iterating this parser, and feed it into another parser.
    fn pipe<P>(self, other: P) -> impls::PipeParser<Self,P> where Self: Sized { impls::PipeParser::new(self,other) }

    /// A parser which produces its input.
    ///
    /// This does its best to avoid having to buffer the input. The result of a buffered parser
    /// may be borrowed (because no buffering was required) or owned (because buffering was required).
    /// Buffering is required in the case that the input was provided in chunks, rather than
    /// contiguously. For example:
    ///
    /// ```
    /// # use parsimonious::{character,Parser,Uncommitted,Stateful};
    /// # use parsimonious::MaybeParseResult::{Commit};
    /// # use parsimonious::ParseResult::{Done,Continue};
    /// # use std::borrow::Cow::{Borrowed,Owned};
    /// fn ignore() {}
    /// let parser = character(char::is_alphabetic).plus(ignore).buffer();
    /// match parser.parse("abc!") {
    ///     Commit(Done("!",result)) => assert_eq!(result,Borrowed("abc")),
    ///     _ => panic!("can't happen"),
    /// }
    /// match parser.parse("abc") {
    ///     Commit(Continue("",parsing)) => match parsing.parse("def!") {
    ///         Done("!",result) => assert_eq!(result,Owned::<'static,str>(String::from("abcdef"))),
    ///         _ => panic!("can't happen"),
    ///     },
    ///     _ => panic!("can't happen"),
    /// }
    /// ```
    fn buffer(self) -> impls::BufferedParser<Self> where Self: Sized { impls::BufferedParser::new(self) }

}

/// A trait for committed parsers.
///
/// A parser is committed if it is guaranteed not to backtrack.
/// Committed parsers are typically constructed by calling the methods of the library,
/// for example:
///
/// ```
/// # use parsimonious::{character,Parser,Uncommitted};
/// let parser = character(char::is_alphanumeric).star(String::new);
/// ```
///
/// Here, `parser` is a `Committed<&str,Output=String>`.
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

pub trait Committed<S>: Parser {

    /// The type of the data being produced by the parser.
    type Output;

    /// The type of the parser state.
    type State: Stateful<S,Output=Self::Output>;

    /// Create a stateful parser by initializing a stateless parser.
    fn init(&self) -> Self::State;

    /// Build an iterator from a parser and some data.
    fn iter(self, data: S) -> impls::IterParser<Self,Self::State,S> where Self: Sized+Copy { impls::IterParser::new(self, data) }

    /// Short hand for calling init then parse.
    fn init_parse(&self, data: S) -> ParseResult<Self::State,S> where Self: Sized { self.init().parse(data) }

    /// Short hand for calling init then done.
    fn init_done(&self) -> Self::Output where Self: Sized { self.init().done() }

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
/// ```
/// # use parsimonious::{character,CHARACTER,Parser,Uncommitted,Committed,Stateful};
/// # use parsimonious::ParseResult::Done;
/// fn default(_: Option<char>) -> String { String::from("?") }
/// let parser =
///    character(char::is_numeric).plus(String::new)
///        .or_else(character(char::is_alphabetic).plus(String::new))
///        .or_else(CHARACTER.map(default));
/// match parser.init().parse("123abc") {
///    Done("abc",result) => assert_eq!(result,"123"),
///    _ => panic!("Can't happen"),
/// }
/// match parser.init().parse("abc123") {
///    Done("123",result) => assert_eq!(result,"abc"),
///    _ => panic!("Can't happen"),
/// }
/// match parser.init().parse("!@#") {
///    Done("@#",result) => assert_eq!(result,"?"),
///    _ => panic!("Can't happen"),
/// }
/// ```
///
/// Semantically, a parser with input *S* and output *T* is a partial function *S\+ → T*
/// whose domain is prefix-closed (that is, if *s·t* is in the domain, then *s* is in the domain).

pub trait Uncommitted<S>: Parser {

    /// The type of the data being produced by the parser.
    type Output;

    /// The type of the parser state.
    type State: Stateful<S,Output=Self::Output>;

    /// Provides data to the parser.
    ///
    /// If `parser: Uncommitted<S,Output=T>`, then `parser.parse(data)` either:
    ///
    /// * returns `Empty(data)` because `data` was empty,
    /// * returns `Abort(data)` because the parser should backtrack, or
    /// * returns `Commit(result)` because the parser has committed.
    ///
    /// For example:
    ///
    /// ```
    /// # use parsimonious::{character,Parser,Uncommitted,Stateful};
    /// # use parsimonious::MaybeParseResult::{Empty,Commit,Abort};
    /// # use parsimonious::ParseResult::{Done,Continue};
    /// let parser = character(char::is_alphabetic).plus(String::new);
    /// match parser.parse("") {
    ///     Empty("") => (),
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
    ///     Commit(Continue("",parsing)) => match parsing.parse("def!") {
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
    fn parse(&self, value: S) -> MaybeParseResult<Self::State,S> where Self: Sized;

}

/// The result of a parse.
pub enum MaybeParseResult<P,S> where P: Stateful<S> {
    /// The input was empty.
    Empty(S),
    /// The parser must backtrack.
    Abort(S),
    /// The parser has committed to parsing the input.
    Commit(ParseResult<P,S>),
}

impl<P,S> MaybeParseResult<P,S> where P: Stateful<S> {
    /// Apply a function the the Commit branch of a parse result
    pub fn map<F,Q>(self, f: F) -> MaybeParseResult<Q,S> where Q: Stateful<S,Output=P::Output>, F: Function<P,Output=Q> {
        match self {
            Empty(rest) => Empty(rest),
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
/// type is `Box<Stateful<S,Output=T>`. There are two issues with this...
///
/// Firstly, the lifetimes mentioned in the type of the parser may change over time.
/// For example, the program:
///
/// ```text
/// fn check_results (self, rest: &'b str, result: String) {
///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
/// }
/// let parser = character(char::is_alphanumeric).star(String::new);
/// let stateful = parser.init();
/// let boxed: Box<Stateful<&'a str,Output=String>> = Box::new(stateful);
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
/// let parser = character(char::is_alphanumeric).star(String::new);
/// let stateful = parser.init();
/// let boxed: Box<for <'a> Stateful<&'a str,Output=String>> = Box::new(stateful);
/// let stuff: &'b str = "abc123!";
/// match boxed.parse(stuff) {
///    Done(rest,result) => self.check_results(rest,result),
///    _ => println!("can't happen"),
/// }
/// ```
///
/// Secondly, the `Stateful` trait is not
/// [object-safe](https://doc.rust-lang.org/book/trait-objects.html#object-safety),
/// so cannot be boxed and unboxed safely. In order to address this, there is a trait
/// `Boxable<S,Output=T>`, which represents stateful parsers, but is object-safe
/// and so can be boxed and unboxed safely:
///
/// ```
/// # struct Foo<'a>(&'a str);
/// # impl<'b> Foo<'b> {
/// fn check_results (self, rest: &'b str, result: String) {
///    assert_eq!(rest,"!"); assert_eq!(result,"abc123");
/// }
/// # fn foo(self) {
/// # use parsimonious::{character,Parser,Uncommitted,Committed,Boxable,Stateful};
/// # use parsimonious::ParseResult::{Done,Continue};
/// let parser = character(char::is_alphanumeric).star(String::new);
/// let stateful = parser.init();
/// let boxed: Box<for <'a> Boxable<&'a str,Output=String>> = Box::new(stateful.boxable());
/// let stuff: &'b str = "abc123!";
/// match boxed.parse(stuff) {
///    Done(rest,result) => self.check_results(rest,result),
///    _ => println!("can't happen"),
/// }
/// # } }
/// ```
///
/// The type `Box<Boxable<S,Output=T>>` implements the trait
/// `Stateful<S,Output=T>`, so boxes can be used as parsers,
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
/// fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Result<Tree,String> {
///     Ok(Tree(children))
/// }
/// let LPAREN = character(is_lparen);
/// let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
/// let TREE = LPAREN
///     .and_then_try(TREE.star(mk_vec))
///     .try_and_then_try(RPAREN)
///     .try_map3(mk_tree);
/// ```
///
/// but this doesn't work because it gives the definition of `TREE` in terms of itself,
/// and Rust doesn't allow this kind of cycle.
///
/// Instead, the solution is to define a struct `TreeParser`, and then implement `Uncommitted<&str>`
/// for it. The type of the state of a `TreeParser` is a box containing an appropriate
/// `BoxableParserState` trait:
///
/// ```
/// # use parsimonious::{Boxable};
/// # struct Tree(Vec<Tree>);
/// type TreeParserState = Box<for<'b> Boxable<&'b str, Output=Tree>>;
/// ```
///
/// The implementation of `Uncommitted<&str>` for `TreeParser` is mostly straightfoward:
///
/// ```
/// # use parsimonious::{character,CHARACTER,Parser,Uncommitted,Committed,Boxable,Stateful,MaybeParseResult};
/// # use parsimonious::ParseResult::{Done,Continue};
/// # use parsimonious::MaybeParseResult::{Commit};
/// # #[derive(Eq,PartialEq,Clone,Debug)]
/// struct Tree(Vec<Tree>);
/// # #[derive(Copy,Clone,Debug)]
/// struct TreeParser;
/// type TreeParserState = Box<for<'b> Boxable<&'b str, Output=Result<Tree,String>>>;
/// impl Parser for TreeParser {}
/// impl<'a> Uncommitted<&'a str> for TreeParser {
///     type Output = Result<Tree,String>;
///     type State = TreeParserState;
///     fn parse(&self, data: &'a str) -> MaybeParseResult<Self::State,&'a str> {
///         // ... parser goes here...`
/// #       fn is_lparen(ch: char) -> bool { ch == '(' }
/// #       fn is_rparen(ch: char) -> bool { ch == ')' }
/// #       fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
/// #       fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
/// #       fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
/// #       fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Result<Tree,String> {
/// #           Ok(Tree(children))
/// #       }
/// #       fn mk_box<P>(parser: P) -> TreeParserState
/// #       where P: 'static+for<'a> Stateful<&'a str, Output=Result<Tree,String>> {
/// #           Box::new(parser.boxable())
/// #       }
/// #       let LPAREN = character(is_lparen);
/// #       let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
/// #       let parser = LPAREN
/// #           .and_then_try(TreeParser.star(mk_vec))
/// #           .try_and_then_try(RPAREN)
/// #           .try_map3(mk_tree);
/// #       parser.parse(data).map(mk_box)
///     }
/// }
/// ```
///
/// The important thing is that the definiton of `parse` can make use of `TREE`, so the parser can call itself
/// recursively, then box up the result state:
///
/// ```
/// # use parsimonious::{character,CHARACTER,Parser,Uncommitted,Committed,Boxable,Stateful,MaybeParseResult};
/// # use parsimonious::ParseResult::{Done,Continue};
/// # use parsimonious::MaybeParseResult::{Commit};
/// # #[derive(Eq,PartialEq,Clone,Debug)]
/// struct Tree(Vec<Tree>);
/// # #[derive(Copy,Clone,Debug)]
/// struct TreeParser;
/// type TreeParserState = Box<for<'b> Boxable<&'b str, Output=Result<Tree,String>>>;
/// impl Parser for TreeParser {}
/// impl<'a> Uncommitted<&'a str> for TreeParser {
///     type Output = Result<Tree,String>;
///     type State = TreeParserState;
///     fn parse(&self, data: &'a str) -> MaybeParseResult<Self::State,&'a str> {
///         fn is_lparen(ch: char) -> bool { ch == '(' }
///         fn is_rparen(ch: char) -> bool { ch == ')' }
///         fn mk_vec() -> Result<Vec<Tree>,String> { Ok(Vec::new()) }
///         fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
///         fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("Expected a ( or ).")) }
///         fn mk_tree(_: char, children: Vec<Tree>, _: char) -> Result<Tree,String> {
///             Ok(Tree(children))
///         }
///         fn mk_box<P>(parser: P) -> TreeParserState
///         where P: 'static+for<'a> Stateful<&'a str, Output=Result<Tree,String>> {
///             Box::new(parser.boxable())
///         }
///         let LPAREN = character(is_lparen);
///         let RPAREN = character(is_rparen).map(mk_ok).or_else(CHARACTER.map(mk_err));
///         let parser = LPAREN
///             .and_then_try(TreeParser.star(mk_vec))
///             .try_and_then_try(RPAREN)
///             .try_map3(mk_tree);
///         parser.parse(data).map(mk_box)
///     }
/// }
/// let TREE = TreeParser;
/// match TREE.parse("((") {
///     Commit(Continue("",parsing)) => match parsing.parse(")()))") {
///         Done(")",result) => assert_eq!(result,Ok(Tree(vec![Tree(vec![]),Tree(vec![])]))),
///          _ => panic!("can't happen"),
///     },
///     _ => panic!("can't happen"),
/// }
/// ```
///
/// The reason for making `Boxable<S>` a different trait from `Stateful<S>`
/// is that it provides weaker safety guarantees. `Stateful<S>` enforces that
/// clients cannot call `parse` after `done`, but `Boxable<S>` does not.

pub trait Boxable<S> {
    type Output;
    fn parse_boxable(&mut self, value: S) -> (S,Option<Self::Output>);
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

/// An uncommitted parser that reads one character.
///
/// The parser `character(f)` reads one character `ch` from the input,
/// if `f(ch)` is `true` then it commits and the result is `ch`,
/// otherwise it backtracks.

pub fn character<F>(f: F) -> impls::CharacterParser<F> where F: Function<char,Output=bool> {
    impls::CharacterParser::new(f)
}

/// A committed parser that reads one character.
///
/// The parser `CHARACTER` reads one character `ch` from the input,
/// and produces `Some(ch)`. It produces `None` at the end of input.

pub const CHARACTER: impls::AnyCharacterParser = impls::AnyCharacterParser;

/// An uncommitted parser that reads one token.
///
/// The parser `token(f)` reads one token `tok` from the input,
/// if `f(tok)` is `true` then it commits and the result is `tok`,
/// otherwise it backtracks.

pub fn token<F>(f: F) -> impls::TokenParser<F> {
    impls::TokenParser::<F>::new(f)
}

/// A committed parser that reads one token.
///
/// The parser `TOKEN` reads one token `tok` from the input,
/// and produces `Some(tok)`. It produces `None` at the end of input.

pub const TOKEN: impls::AnyTokenParser = impls::AnyTokenParser;

pub mod impls {

    //! Provide implementations of parser traits.

    use super::{Stateful,Parser,Uncommitted,Committed,Boxable,ParseResult,MaybeParseResult,Factory,Function,Consumer};
    use super::ParseResult::{Continue,Done};
    use super::MaybeParseResult::{Abort,Commit,Empty};

    use self::AndThenStatefulParser::{InLhs,InRhs};
    use self::OrElseStatefulParser::{Lhs,Rhs};
    use self::OrElseCommittedParser::{Uncommit,CommitLhs,CommitRhs};
    use self::OrEmitStatefulParser::{Unresolved,Resolved};

    use std::borrow::Cow;
    use std::borrow::Cow::{Borrowed,Owned};

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
    impl<P,F,S,T> Stateful<S> for MapStatefulParser<P,F> where P: Stateful<S,Output=T>, F: Function<T> {
        type Output = F::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self.0.parse(value) {
                Done(rest,result) => Done(rest,self.1.apply(result)),
                Continue(rest,parsing) => Continue(rest,MapStatefulParser(parsing,self.1)),
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

    impl<P,F> Parser for MapParser<P,F> {}
    impl<P,F,S> Uncommitted<S> for MapParser<P,F> where P: Uncommitted<S>, F: Copy+Function<P::Output> {
        type Output = F::Output;
        type State = MapStatefulParser<P::State,F>;
        fn parse(&self, value: S) -> MaybeParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty(rest) => Empty(rest),
                Commit(Done(rest,result)) => Commit(Done(rest,self.1.apply(result))),
                Commit(Continue(rest,parsing)) => Commit(Continue(rest,MapStatefulParser(parsing,self.1))),
                Abort(value) => Abort(value),
            }
        }
    }
    impl<P,F,S> Committed<S> for MapParser<P,F> where P: Committed<S>, F: Copy+Function<P::Output> {
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

    impl<P,Q> Parser for AndThenParser<P,Q> {}
    impl<P,Q,S> Committed<S> for AndThenParser<P,Q> where P: Committed<S>, Q: Committed<S> {
        type Output = (P::Output,Q::Output);
        type State = AndThenStatefulParser<P::State,Q::State,P::Output>;
        fn init(&self) -> Self::State {
            InLhs(self.0.init(),self.1.init())
        }
    }
    impl<P,Q,S> Uncommitted<S> for AndThenParser<P,Q> where P: Uncommitted<S>, Q: Committed<S> {
        type Output = (P::Output,Q::Output);
        type State = AndThenStatefulParser<P::State,Q::State,P::Output>;
        fn parse(&self, value: S) -> MaybeParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty(rest) => Empty(rest),
                Commit(Done(rest,result1)) => match self.1.init().parse(rest) {
                    Done(rest,result2) => Commit(Done(rest,(result1,result2))),
                    Continue(rest,parsing) => Commit(Continue(rest,InRhs(result1,parsing))),
                },
                Commit(Continue(rest,parsing)) => Commit(Continue(rest,InLhs(parsing,self.1.init()))),
                Abort(value) => Abort(value),
            }
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub enum AndThenStatefulParser<P,Q,T> {
        InLhs(P,Q),
        InRhs(T,Q),
    }

    impl<P,Q,S> Stateful<S> for AndThenStatefulParser<P,Q,P::Output> where P: Stateful<S>, Q: Stateful<S> {
        type Output = (P::Output,Q::Output);
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                InLhs(lhs,rhs) => {
                    match lhs.parse(value) {
                        Done(rest,result1) => match rhs.parse(rest) {
                            Done(rest,result2) => Done(rest,(result1,result2)),
                            Continue(rest,parsing) => Continue(rest,InRhs(result1,parsing)),
                        },
                        Continue(rest,parsing) => Continue(rest,InLhs(parsing,rhs)),
                    }
                },
                InRhs(result1,rhs) => {
                    match rhs.parse(value) {
                        Done(rest,result2) => Done(rest,(result1,result2)),
                        Continue(rest,parsing) => Continue(rest,InRhs(result1,parsing)),
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
    pub struct OrElseParser<P,Q>(P,Q);

    impl<P,Q> Parser for OrElseParser<P,Q> {}
    impl<P,Q,S> Committed<S> for OrElseParser<P,Q> where P: Copy+Uncommitted<S>, Q: Committed<S,Output=P::Output> {
        type Output = P::Output;
        type State = OrElseCommittedParser<P,P::State,Q::State>;
        fn init(&self) -> Self::State {
            Uncommit(self.0,self.1.init())
        }
    }
    impl<P,Q,S> Uncommitted<S> for OrElseParser<P,Q> where P: Uncommitted<S>, Q: Uncommitted<S,Output=P::Output> {
        type Output = P::Output;
        type State = OrElseStatefulParser<P::State,Q::State>;
        fn parse(&self, value: S) -> MaybeParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty(rest) => Empty(rest),
                Commit(Done(rest,result)) => Commit(Done(rest,result)),
                Commit(Continue(rest,parsing)) => Commit(Continue(rest,Lhs(parsing))),
                Abort(value) => match self.1.parse(value) {
                    Empty(rest) => Empty(rest),
                    Commit(Done(rest,result)) => Commit(Done(rest,result)),
                    Commit(Continue(rest,parsing)) => Commit(Continue(rest,Rhs(parsing))),
                    Abort(value) => Abort(value),
                }
            }
        }
    }

    impl<P,Q> OrElseParser<P,Q> {
        pub fn new(lhs: P, rhs: Q) -> Self {
            OrElseParser(lhs,rhs)
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub enum OrElseStatefulParser<P,Q> {
        Lhs(P),
        Rhs(Q),
    }

    impl<P,Q,S> Stateful<S> for OrElseStatefulParser<P,Q> where P: Stateful<S>, Q: Stateful<S,Output=P::Output> {
        type Output = P::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                Lhs(lhs) => {
                    match lhs.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(rest,parsing) => Continue(rest,Lhs(parsing)),
                    }
                },
                Rhs(rhs) => {
                    match rhs.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(rest,parsing) => Continue(rest,Rhs(parsing)),
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

    #[derive(Copy, Clone, Debug)]
    pub enum OrElseCommittedParser<P,Q,R> {
        Uncommit(P,R),
        CommitLhs(Q),
        CommitRhs(R),
    }

    impl<P,Q,S> Stateful<S> for OrElseCommittedParser<P,P::State,Q> where P: Uncommitted<S>, Q: Stateful<S,Output=P::Output> {
        type Output = P::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                Uncommit(lhs, rhs) => {
                    match lhs.parse(value) {
                        Empty(value) => Continue(value,Uncommit(lhs,rhs)),
                        Commit(Done(rest,result)) => Done(rest,result),
                        Commit(Continue(rest,parsing)) => Continue(rest,CommitLhs(parsing)),
                        Abort(value) => match rhs.parse(value) {
                            Done(rest,result) => Done(rest,result),
                            Continue(rest,parsing) => Continue(rest,CommitRhs(parsing)),
                        }
                    }
                },
                CommitLhs(lhs) => {
                    match lhs.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(rest,parsing) => Continue(rest,CommitLhs(parsing)),
                    }
                },
                CommitRhs(rhs) => {
                    match rhs.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(rest,parsing) => Continue(rest,CommitRhs(parsing)),
                    }
                },
            }
        }
        fn done(self) -> Self::Output {
            match self {
                Uncommit(_,rhs) => rhs.done(),
                CommitLhs(lhs) => lhs.done(),
                CommitRhs(rhs) => rhs.done(),
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

    impl<P,F,S> Stateful<S> for OrEmitStatefulParser<P,F,P::State> where P: Uncommitted<S>, F: Factory<Output=P::Output> {
        type Output = P::Output;
        fn parse(self, value: S) -> ParseResult<Self,S> {
            match self {
                Unresolved(parser,default) => {
                    match parser.parse(value) {
                        Empty(rest) => Continue(rest,Unresolved(parser,default)),
                        Commit(Done(rest,result)) => Done(rest,result),
                        Commit(Continue(rest,parsing)) => Continue(rest,Resolved(parsing)),
                        Abort(value) => Done(value,default.build()),
                    }
                },
                Resolved(parser) => {
                    match parser.parse(value) {
                        Done(rest,result) => Done(rest,result),
                        Continue(rest,parsing) => Continue(rest,Resolved(parsing)),
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

    impl<P,F> Parser for OrEmitParser<P,F> {}
    impl<P,F,S> Committed<S> for OrEmitParser<P,F> where P: Clone+Uncommitted<S>, F: Copy+Factory<Output=P::Output> {
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

    impl<P,T,S> Stateful<S> for StarStatefulParser<P,P::State,T> where P: Copy+Uncommitted<S>, T: Consumer<P::Output> {
        type Output = T;
        fn parse(mut self, mut value: S) -> ParseResult<Self,S> {
            loop {
                match self.1.take() {
                    None => match self.0.parse(value) {
                        Empty(rest) => return Continue(rest,StarStatefulParser(self.0,None,self.2)),
                        Commit(Continue(rest,parsing)) => return Continue(rest,StarStatefulParser(self.0,Some(parsing),self.2)),
                        Commit(Done(rest,result)) => { self.2.accept(result); value = rest; },
                        Abort(rest) => return Done(rest,self.2),
                    },
                    Some(parser) => match parser.parse(value) {
                        Continue(rest,parsing) => return Continue(rest,StarStatefulParser(self.0,Some(parsing),self.2)),
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

    impl<P,F> Parser for PlusParser<P,F> {}
    impl<P,F,S> Uncommitted<S> for PlusParser<P,F> where P: Copy+Uncommitted<S>, F: Factory, F::Output: Consumer<P::Output> {
        type Output = F::Output;
        type State = StarStatefulParser<P,P::State,F::Output>;
        fn parse(&self, value: S) -> MaybeParseResult<Self::State,S> {
            match self.0.parse(value) {
                Empty(rest) => Empty(rest),
                Abort(rest) => Abort(rest),
                Commit(Continue(rest,parsing)) => Commit(Continue(rest,StarStatefulParser(self.0,Some(parsing),self.1.build()))),
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

    impl<P,F> Parser for StarParser<P,F> {}
    impl<P,F,S> Committed<S> for StarParser<P,F> where P: Copy+Uncommitted<S>, F: Factory, F::Output: Consumer<P::Output> {
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

    // ----------- A type for empty parsers -------------

    #[derive(Copy, Clone, Debug)]
    enum Impossible{}

    impl Impossible {
        fn cant_happen<T>(&self) -> T {
            match *self {}
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct ImpossibleStatefulParser<T>(Impossible,T);

    impl<T,S> Stateful<S> for ImpossibleStatefulParser<T> {
        type Output = T;
        fn parse(self, _: S) -> ParseResult<Self,S> {
            self.0.cant_happen()
        }
        fn done(self) -> T {
            self.0.cant_happen()
        }
    }

    // ----------- Character parsers -------------

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

    impl<F> Parser for CharacterParser<F> {}
    impl<'a,F> Uncommitted<&'a str> for CharacterParser<F> where F: Function<char,Output=bool> {
        type Output = char;
        type State = ImpossibleStatefulParser<char>;
        fn parse(&self, value: &'a str) -> MaybeParseResult<Self::State,&'a str> {
            match value.chars().next() {
                None => Empty(value),
                Some(ch) if self.0.apply(ch) => {
                    let len = ch.len_utf8();
                    Commit(Done(&value[len..],ch))
                },
                Some(_) => Abort(value),
            }
        }
    }

    impl<F> CharacterParser<F> {
        pub fn new(function: F) -> Self {
            CharacterParser(function)
        }
    }

    #[derive(Copy,Clone,Debug)]
    pub struct AnyCharacterParser;

    impl Parser for AnyCharacterParser {}
    impl<'a> Stateful<&'a str> for AnyCharacterParser {
        type Output = Option<char>;
        fn parse(self, value: &'a str) -> ParseResult<Self,&'a str> {
            match value.chars().next() {
                None => Continue(value,AnyCharacterParser),
                Some(ch) => {
                    let len = ch.len_utf8();
                    Done(&value[len..],Some(ch))
                },
            }
        }
        fn done(self) -> Self::Output {
            None
        }
    }
    impl<'a> Committed<&'a str> for AnyCharacterParser {
        type Output = Option<char>;
        type State = Self;
        fn init(&self) -> Self {
            AnyCharacterParser
        }
    }

    // ----------- Token parsers -------------

    #[derive(Debug)]
    pub struct TokenParser<F>(F);

    // A work around for functions implmenting copy but not clone
    // https://github.com/rust-lang/rust/issues/28229
    impl<F> Copy for TokenParser<F> where F: Copy {}
    impl<F> Clone for TokenParser<F> where F: Copy {
        fn clone(&self) -> Self {
            TokenParser(self.0)
        }
    }

    impl<F> Parser for TokenParser<F> {}
    impl<F,I> Uncommitted<Peekable<I>> for TokenParser<F> where
        F: for<'a> Function<&'a I::Item,Output=bool>,
        I: Iterator,
    {
        type Output = I::Item;
        type State = ImpossibleStatefulParser<I::Item>;
        fn parse(&self, mut iterator: Peekable<I>) -> MaybeParseResult<Self::State,Peekable<I>> {
            let matched = match iterator.peek() {
                None => None,
                Some(tok) => Some(self.0.apply(tok)),
            };
            match matched {
                None => Empty(iterator),
                Some(true) => {
                    let tok = iterator.next().unwrap();
                    Commit(Done(iterator,tok))
                },
                Some(false) => Abort(iterator),
            }
        }
    }

    impl<F> TokenParser<F> {
        pub fn new(function: F) -> Self {
            TokenParser(function)
        }
    }

    #[derive(Copy,Clone,Debug)]
    pub struct AnyTokenParser;

    impl Parser for AnyTokenParser {}
    impl<I> Stateful<I> for AnyTokenParser where I: Iterator {
        type Output = Option<I::Item>;
        fn parse(self, mut iter: I) -> ParseResult<Self,I> {
            match iter.next() {
                None => Continue(iter,AnyTokenParser),
                Some(tok) => Done(iter,Some(tok)),
            }
        }
        fn done(self) -> Self::Output {
            None
        }
    }
    impl<I> Committed<I> for AnyTokenParser where I: Iterator {
        type Output = Option<I::Item>;
        type State = Self;
        fn init(&self) -> Self {
            AnyTokenParser
        }
    }

    // ----------- Buffering -------------

    // If m is a Uncommitted<&'a str>, then
    // m.buffer() is a Uncommitted<&'a str> with Output Cow<'a,str>.
    // It does as little buffering as it can, but it does allocate as buffer for the case
    // where the boundary marker of the input is misaligned with that of the parser.
    // For example, m is matching string literals, and the input is '"abc' followed by 'def"'
    // we have to buffer up '"abc'.

    // TODO(ajeffrey): make this code generic.

    #[derive(Copy, Clone, Debug)]
    pub struct BufferedParser<P>(P);

    impl<P> Parser for BufferedParser<P> {}
    impl<'a,P> Uncommitted<&'a str> for BufferedParser<P> where P: Uncommitted<&'a str> {
        type Output = Cow<'a,str>;
        type State = BufferedStatefulParser<P::State>;
        fn parse(&self, value: &'a str) -> MaybeParseResult<Self::State,&'a str> {
            match self.0.parse(value) {
                Empty(rest) => Empty(rest),
                Commit(Done(rest,_)) => Commit(Done(rest,Borrowed(&value[..(value.len() - rest.len())]))),
                Commit(Continue(rest,parsing)) => Commit(Continue(rest,BufferedStatefulParser(parsing,String::from(value)))),
                Abort(value) => Abort(value),
            }
        }
    }

    impl<P> BufferedParser<P> {
        pub fn new(parser: P) -> Self {
            BufferedParser(parser)
        }
    }

    #[derive(Clone,Debug)]
    pub struct BufferedStatefulParser<P>(P,String);

    impl<'a,P> Stateful<&'a str> for BufferedStatefulParser<P> where P: Stateful<&'a str> {
        type Output = Cow<'a,str>;
        fn parse(mut self, value: &'a str) -> ParseResult<Self,&'a str> {
            match self.0.parse(value) {
                Done(rest,_) => { self.1.push_str(&value[..(value.len() - rest.len())]); Done(rest,Owned(self.1)) },
                Continue(rest,parsing) => { self.1.push_str(value); Continue(rest,BufferedStatefulParser(parsing,self.1)) },
            }
        }
        fn done(self) -> Self::Output {
            Owned(self.1)
        }
    }

    // ----------- Parsers which are boxable -------------

    pub struct BoxableParser<P> (Option<P>);
    impl<P,S> Boxable<S> for BoxableParser<P> where P: Stateful<S> {
        type Output = P::Output;
        fn parse_boxable(&mut self, value: S) -> (S,Option<Self::Output>) {
            match self.0.take().unwrap().parse(value) {
                Done(rest,result) => (rest,Some(result)),
                Continue(rest,parsing) => { self.0 = Some(parsing); (rest,None) },
            }
        }
        fn done_boxable(&mut self) -> Self::Output {
            self.0.take().unwrap().done()
        }
    }

    impl<P:?Sized,S> Stateful<S> for Box<P> where P: Boxable<S> {
        type Output = P::Output;
        fn parse(mut self, value: S) -> ParseResult<Self,S> {
            match self.parse_boxable(value) {
                (rest,Some(result)) => Done(rest,result),
                (rest,None) => Continue(rest,self),
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

    // ----------- Cut-and-paste Peekable -------------

    // Rather annoyingly, we need access to a private field, so we just copy the source.
    // TOD: Fix this!

    #[derive(Clone)]
    pub struct Peekable<I> where I: Iterator {
        iter: I,
        peeked: Option<I::Item>,
    }

    impl<I> Iterator for Peekable<I> where I: Iterator {
        type Item = I::Item;
        #[inline]
        fn next(&mut self) -> Option<I::Item> {
            match self.peeked {
                Some(_) => self.peeked.take(),
                None => self.iter.next(),
            }
        }
    }

    impl<I> Peekable<I> where I: Iterator{
        pub fn new(iter: I) -> Self {
            Peekable{ iter: iter, peeked: None }
        }
        #[inline]
        pub fn peek(&mut self) -> Option<&I::Item> {
            if self.peeked.is_none() {
                self.peeked = self.iter.next();
            }
            match self.peeked {
                Some(ref value) => Some(value),
                None => None,
            }
        }
    }

    // ----------- Iterate over parse results -------------

    #[derive(Copy, Clone, Debug)]
    pub struct IterParser<P,Q,S>(P,Option<(Q,S)>);

    impl<P,S> Iterator for IterParser<P,P::State,S> where P: Copy+Committed<S> {
        type Item = P::Output;
        fn next(&mut self) -> Option<P::Output> {
            let (state, result) = match self.1.take() {
                None => (None, None),
                Some((parsing, data)) => match parsing.parse(data) {
                    Done(rest, result) => (Some((self.0.init(), rest)), Some(result)),
                    Continue(rest, parsing) => (Some((parsing, rest)), None),
                }
            };
            *self = IterParser(self.0,state);
            result
        }
    }

    impl<P,S> IterParser<P,P::State,S> where P: Copy+Committed<S> {
        pub fn new(parser: P, data: S) -> Self {
            IterParser(parser, Some((parser.init(), data)))
        }
    }

    // ----------- Pipe parsers -------------

    #[derive(Copy, Clone, Debug)]
    pub struct PipeStateful<P,Q,R>(P,Q,R);

    impl<P,Q,S> Stateful<S> for PipeStateful<P,P::State,Q> where
        P: Copy+Committed<S>,
        Q: Stateful<Peekable<IterParser<P,P::State,S>>>,
    {
        type Output = Q::Output;
        fn parse(self, data: S) -> ParseResult<Self,S> {
            let iter = IterParser(self.0,Some((self.1,data)));
            match self.2.parse(Peekable::new(iter)) {
                Done(iter, result) => Done(iter.iter.1.unwrap().1, result),
                Continue(iter, parsing2) => {
                    let (parsing1, data) = iter.iter.1.unwrap();
                    Continue(data, PipeStateful(self.0, parsing1, parsing2))
                }
            }
        }
        fn done(self) -> Q::Output {
            // TODO: feed the output of self.1.done() into self.2.
            self.1.done();
            self.2.done()
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub struct PipeParser<P,Q>(P,Q);

    impl<P,Q> Parser for PipeParser<P,Q> {}
    impl<P,Q,S> Committed<S> for PipeParser<P,Q> where
        P: Copy+Committed<S>,
        Q: Committed<Peekable<IterParser<P,P::State,S>>>,
    {
        type State = PipeStateful<P,P::State,Q::State>;
        type Output = Q::Output;
        fn init(&self) -> Self::State {
            PipeStateful(self.0, self.0.init(), self.1.init())
        }
    }

    impl<P,Q> PipeParser<P,Q> {
        pub fn new(lhs: P, rhs: Q) -> Self {
            PipeParser(lhs,rhs)
        }
    }

}

// ----------- Tests -------------

#[allow(non_snake_case,dead_code)]
impl<P,S> MaybeParseResult<P,S> where P: Stateful<S> {

    fn unEmpty(self) -> S {
        match self {
            Empty(rest) => rest,
            _     => panic!("MaybeParseResult is not empty"),
        }
    }

    fn unAbort(self) -> S {
        match self {
            Abort(s) => s,
            _        => panic!("MaybeParseResult is not failure"),
        }
    }

    fn unCommit(self) -> ParseResult<P,S> {
        match self {
            Commit(s) => s,
            _       => panic!("MaybeParseResult is not success"),
        }
    }

}

#[allow(non_snake_case,dead_code)]
impl<P,S> ParseResult<P,S> where P: Stateful<S> {

    fn unDone(self) -> (S,P::Output) {
        match self {
            Done(s,t) => (s,t),
            _         => panic!("ParseResult is not done"),
        }
    }

    fn unContinue(self) -> P {
        match self {
            Continue(_,p) => p,
            _           => panic!("ParseResult is not continue"),
        }
    }

}

#[test]
fn test_character() {
    let parser = character(char::is_alphabetic);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("abc").unCommit().unDone(),("bc",'a'));
}

#[test]
#[allow(non_snake_case)]
fn test_CHARACTER() {
    let parser = CHARACTER;
    assert_eq!(parser.init().parse("abc").unDone(),("bc",Some('a')));
    assert_eq!(parser.init().parse("").unContinue().parse("abc").unDone(),("bc",Some('a')));
    assert_eq!(parser.init().done(),None);
}

#[test]
fn test_token() {
    fn is_zero(num: &usize) -> bool { *num == 0 }
    let parser = token(is_zero);
    let mut iter = parser.parse(impls::Peekable::new((1..3))).unAbort();
    assert_eq!(iter.next(),Some(1));
    assert_eq!(iter.next(),Some(2));
    assert_eq!(iter.next(),None);
    let (mut iter, result) = parser.parse(impls::Peekable::new((0..3))).unCommit().unDone();
    assert_eq!(iter.next(),Some(1));
    assert_eq!(iter.next(),Some(2));
    assert_eq!(iter.next(),None);
    assert_eq!(result,0);
}

#[test]
#[allow(non_snake_case)]
fn test_TOKEN() {
    let parser = TOKEN;
    let (mut iter, result) = parser.init_parse("abc".chars()).unDone();
    assert_eq!(result, Some('a'));
    assert_eq!(iter.next(), Some('b'));
    assert_eq!(iter.next(), Some('c'));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_map() {
    let parser = character(char::is_alphabetic).map(Some);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("abc").unCommit().unDone(),("bc",Some('a')));
}

#[test]
#[allow(non_snake_case)]
fn test_map2() {
    fn f(ch1: char, ch2: Option<char>) -> Option<(char, char)> {
        ch2.and_then(|ch2| Some((ch1,ch2)))
    }
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).map2(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("!b!").unAbort(),"!b!");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("ab!").unCommit().unDone(),("!",Some(('a','b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_map3() {
    fn f(ch1: char, ch2: Option<char>, ch3: Option<char>) -> Option<(char, char, char)> {
        ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1,ch2,ch3))))
    }
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).map3(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("!bc!").unAbort(),"!bc!");
    assert_eq!(parser.parse("a!c!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("ab!!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("abc!").unCommit().unDone(),("!",Some(('a','b','c'))));
}

#[test]
#[allow(non_snake_case)]
fn test_map4() {
    fn f(ch1: char, ch2: Option<char>, ch3: Option<char>, ch4: Option<char>) -> Option<(char, char, char, char)> {
        ch4.and_then(|ch4| ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1,ch2,ch3,ch4)))))
    }
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).map4(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("!bcd!").unAbort(),"!bcd!");
    assert_eq!(parser.parse("a!cd!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("ab!d!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("abc!!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("abcd!").unCommit().unDone(),("!",Some(('a','b','c','d'))));
}

#[test]
#[allow(non_snake_case)]
fn test_map5() {
    fn f(ch1: char, ch2: Option<char>, ch3: Option<char>, ch4: Option<char>, ch5: Option<char>) -> Option<(char, char, char, char, char)> {
        ch5.and_then(|ch5| ch4.and_then(|ch4| ch3.and_then(|ch3| ch2.and_then(|ch2| Some((ch1,ch2,ch3,ch4,ch5))))))
    }
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).and_then(ALPHANUMERIC).map5(f);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("!bcde!").unAbort(),"!bcde!");
    assert_eq!(parser.parse("a!cde!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("ab!de!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("abc!e!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("abcd!!").unCommit().unDone(),("!",None));
    assert_eq!(parser.parse("abcde!").unCommit().unDone(),("!",Some(('a','b','c','d','e'))));
}

#[test]
#[allow(non_snake_case)]
fn test_and_then() {
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_else(CHARACTER.map(mk_none));
    let ALPHABETIC = character(char::is_alphabetic).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = ALPHABETIC.and_then(ALPHANUMERIC);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("989").unDone(),("9",(None,Some('8'))));
    assert_eq!(parser.init().parse("a!!").unDone(),("!",(Some('a'),None)));
    assert_eq!(parser.init().parse("abc").unDone(),("c",(Some('a'),Some('b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then() {
    fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = character(char::is_alphabetic).map(mk_ok).try_and_then(ALPHANUMERIC);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!",Ok(('a',Err(String::from("oh"))))));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Ok(('a',Ok('b')))));
}

#[test]
#[allow(non_snake_case)]
fn test_and_then_try() {
    fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = character(char::is_alphabetic).map(mk_ok).and_then_try(ALPHANUMERIC);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!",Err(String::from("oh"))));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Ok((Ok('a'),'b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_try_and_then_try() {
    fn mk_err<T>(_: Option<char>) -> Result<T,String> { Err(String::from("oh")) }
    fn mk_ok<T>(ok: T) -> Result<T,String> { Ok(ok) }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(mk_ok).or_else(CHARACTER.map(mk_err));
    let parser = character(char::is_alphabetic).map(mk_ok).try_and_then_try(ALPHANUMERIC);
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!!").unCommit().unDone(),("!",Err(String::from("oh"))));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Ok(('a','b'))));
}

#[test]
#[allow(non_snake_case)]
fn test_or_else() {
    fn mk_none<T>(_: Option<char>) -> Option<T> { None }
    let NUMERIC = character(char::is_numeric).map(Some).or_else(CHARACTER.map(mk_none));
    let ALPHABETIC = character(char::is_alphabetic).map(Some).or_else(CHARACTER.map(mk_none));
    let parser = character(char::is_alphabetic).and_then(ALPHABETIC).map(Some).
        or_else(character(char::is_numeric).and_then(NUMERIC).map(Some)).
        or_else(CHARACTER.map(mk_none));
    parser.init().parse("").unContinue();
    parser.init().parse("a").unContinue();
    parser.init().parse("9").unContinue();
    assert_eq!(parser.init().parse("!!").unDone(),("!",None));
    assert_eq!(parser.init().parse("a99").unDone(),("9",Some(('a',None))));
    assert_eq!(parser.init().parse("9aa").unDone(),("a",Some(('9',None))));
    assert_eq!(parser.init().parse("abc").unDone(),("c",Some(('a',Some('b')))));
    assert_eq!(parser.init().parse("123").unDone(),("3",Some(('1',Some('2')))));
}

#[test]
#[allow(non_snake_case)]
fn test_plus() {
    let parser = character(char::is_alphanumeric).plus(String::new);
    parser.parse("").unEmpty();
    parser.parse("!!!").unAbort();
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",String::from("a")));
    assert_eq!(parser.parse("abc98def!").unCommit().unDone(),("!",String::from("abc98def")));
}

#[test]
#[allow(non_snake_case)]
fn test_star() {
    let parser = character(char::is_alphanumeric).star(String::new);
    parser.init().parse("").unContinue();
    assert_eq!(parser.init().parse("!!!").unDone(),("!!!",String::from("")));
    assert_eq!(parser.init().parse("a!").unDone(),("!",String::from("a")));
    assert_eq!(parser.init().parse("abc98def!").unDone(),("!",String::from("abc98def")));
}

#[test]
#[allow(non_snake_case)]
fn test_buffer() {
    use std::borrow::Cow::{Borrowed,Owned};
    fn ignore() {}
    let ALPHABETIC = character(char::is_alphabetic);
    let ALPHANUMERIC = character(char::is_alphanumeric);
    let parser = ALPHABETIC.and_then(ALPHANUMERIC.star(ignore)).buffer();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",Borrowed("a")));
    assert_eq!(parser.parse("abc!").unCommit().unDone(),("!",Borrowed("abc")));
    let parsing = parser.parse("a").unCommit().unContinue();
    assert_eq!(parsing.parse("bc!").unDone(),("!",Owned(String::from("abc"))));
}

#[test]
#[allow(non_snake_case)]
fn test_iter() {
    fn mk_X(_: Option<char>) -> char { 'X' }
    let ALPHABETIC = character(char::is_alphabetic);
    let parser = ALPHABETIC.or_else(CHARACTER.map(mk_X));
    let mut iter = parser.iter("abc");
    assert_eq!(iter.next(),Some('a'));
    assert_eq!(iter.next(),Some('b'));
    assert_eq!(iter.next(),Some('c'));
    assert_eq!(iter.next(),None);
}

#[test]
#[allow(non_snake_case)]
fn test_pipe() {
    use std::borrow::{Borrow,Cow};
    #[derive(Clone,Debug,PartialEq,Eq)]
    enum Token { Identifier(String), Number(usize), Other }
    fn mk_id<'a>(string: Cow<'a,str>) -> Token { Token::Identifier(string.into_owned()) }
    fn mk_num<'a>(string: Cow<'a,str>) -> Token { Token::Number(usize::from_str_radix(string.borrow(),10).unwrap()) }
    fn mk_other(_: Option<char>) -> Token { Token::Other }
    fn ignore() {}
    fn is_decimal(ch: char) -> bool { ch.is_digit(10) }
    fn is_identifier(tok: &Token) -> bool { match *tok { Token::Identifier(_) => true, _ => false } }
    fn is_number(tok: &Token) -> bool { match *tok { Token::Number(_) => true, _ => false } }
    let ALPHABETIC = character(char::is_alphabetic);
    let DIGIT = character(is_decimal);
    let lexer = ALPHABETIC.plus(ignore).buffer().map(mk_id)
        .or_else(DIGIT.plus(ignore).buffer().map(mk_num))
        .or_else(CHARACTER.map(mk_other));
    let parser = token(is_identifier).or_else(token(is_number)).star(Vec::<Token>::new);
    assert_eq!(lexer.pipe(parser).init().parse("abc37!!").unDone(), ("!",vec![ Token::Identifier(String::from("abc")), Token::Number(37) ]));
}

#[test]
#[allow(non_snake_case)]
fn test_different_lifetimes() {
    fn go<'a,'b,P>(ab: &'a str, cd: &'b str, parser: P) where P: Copy+for<'c> Committed<&'c str,Output=(Option<char>,Option<char>)> {
        let _: &'a str = parser.init().parse(ab).unDone().0;
        let _: &'b str = parser.init().parse(cd).unDone().0;
        assert_eq!(parser.init().parse(ab).unDone(),("",(Some('a'),Some('b'))));
        assert_eq!(parser.init().parse(cd).unDone(),("",(Some('c'),Some('d'))));
    }
    let parser = CHARACTER.and_then(CHARACTER);
    go("ab","cd",parser);
}
