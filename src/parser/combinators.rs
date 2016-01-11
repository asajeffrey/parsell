use std::mem;

use self::BufferedParserState::{Beginning, Middle, EndMatch, EndFail};
use self::MatchResult::{Undecided, Matched, Failed};
use self::ConstantParserState::{AtOffset, AtEndMatched, AtEndFailed};

use std::marker::PhantomData;

// ----------- Types with lifetimes -------------

// Borrowing encoding of paramaterized types from
// https://github.com/rust-lang/rfcs/blob/master/text/0195-associated-items.md#encoding-higher-kinded-types

pub trait TypeWithLifetime<'a> {
    type Type;
}

pub type At<'a,T> where T: TypeWithLifetime<'a> = T::Type;

pub struct Always<T> (PhantomData<T>);

impl<'a,T> TypeWithLifetime<'a> for Always<T> {
    type Type = T;
}

pub type Unit = Always<()>;

// ----------- Types for consumers ------------

pub trait Consumer<T> where T: for<'a> TypeWithLifetime<'a> {
    fn accept<'a>(&mut self, arg: At<'a,T>);
}

impl<T,F> Consumer<T> for F where T: for<'a> TypeWithLifetime<'a>, F: for<'a> FnMut(At<'a,T>) {
    fn accept<'a>(&mut self, arg: At<'a,T>) {
        self(arg)
    }
}

struct DiscardConsumer<T> (PhantomData<T>);

impl<T> Consumer<T> for DiscardConsumer<T> where T: for<'a> TypeWithLifetime<'a> {
    fn accept<'a>(&mut self, _: At<'a,T>) {}
}

impl<T> DiscardConsumer<T> {
    fn new() -> DiscardConsumer<T> {
        DiscardConsumer(PhantomData)
    }
}

// ----------- Types for parsers ------------

// State machine transitions are:
//
// init -Undecided(true)->  init
// init -Undecided(false)-> committed
// init -Matched(s)->       matched
// init -Failed(s)->        failed
//
// committed -Undecided(false)-> committed
// committed -Matched(s)->       matched
// committed -Failed(false)->    failed(false)
//
// matched -Matched(s)-> matched
//
// failed -Failed(s)-> failed
//
// The Failed(s) action carries a Option<T> indicating if backtracking is allowed,
// and if so, the value to backtrack with.

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum MatchResult<T> {
    Undecided,
    Matched(Option<T>),
    Failed(Option<T>),
}

pub trait Parser<S,T> where S: for<'a> TypeWithLifetime<'a>, T: for<'a> TypeWithLifetime<'a> {
    // If push_to returns Failed(Some(s)), it is side-effect-free
    // push_to should be called with non-empty input,
    // when it returns Matched(Some(s)) or Failed(Some(s)) then s is non-empty.
    // In the case where T is "list-like" (e.g. &str or &[T])
    // push_to(a ++ b, d) is the same as push_to(a,d); push_to(b,d)
    fn push_to<'a,D>(&mut self, value: At<'a,S>, downstream: &mut D) -> MatchResult<At<'a,S>> where D: Consumer<T>;
    // Resets the parser state back to its initial state
    // Returns true if there was a match.
    fn done_to<D>(&mut self, downstream: &mut D) -> bool where D: Consumer<T>;
    // Helper methods
    fn push<'a>(&mut self, value: At<'a,S>) -> MatchResult<At<'a,S>> {
        self.push_to(value, &mut DiscardConsumer::new())
    }
    fn done(&mut self) -> bool {
        self.done_to(&mut DiscardConsumer::new())
    }
    fn and_then<R>(self, other: R) -> AndThenParser<Self,R> where Self: Sized, R: Parser<S,T> {
        AndThenParser{ lhs: self, rhs: CommittedParser{ parser: other }, in_lhs: true }
    }
    fn or_else<R>(self, other: R) -> OrElseParser<Self,R> where Self: Sized, R: Parser<S,T> {
        OrElseParser{ lhs: self, rhs: other, in_lhs: true }
    }
    fn star(self) -> StarParser<Self> where Self: Sized {
        StarParser{ parser: self, matched: true, first_time: true }
    }
}

pub trait BufferableMatcher<S,T> where S: for<'a> TypeWithLifetime<'a>, T: Parser<S,S> {
    fn buffer(self) -> T;
}

// ----------- Always commit ---------------

#[derive(Clone, Debug)]
pub struct CommittedParser<P> {
    parser: P,
}

impl<S,T,P> Parser<S,T> for CommittedParser<P> where P: Parser<S,T>, S: for<'a> TypeWithLifetime<'a>, T: for<'a> TypeWithLifetime<'a>  {
    fn push_to<'a,D>(&mut self, value: At<'a,S>, downstream: &mut D) -> MatchResult<At<'a,S>> where D: Consumer<T> {
        match self.parser.push_to(value, downstream) {
            Undecided     => Undecided,
            Matched(rest) => Matched(rest),
            Failed(_)     => Failed(None),
        }
    }
    fn done_to<D>(&mut self, downstream: &mut D) -> bool where D: Consumer<T> {
        self.parser.done_to(downstream)
    }
}

// ----------- Sequencing ---------------

#[derive(Clone, Debug)]
pub struct AndThenParser<L,R> {
    lhs: L,
    rhs: CommittedParser<R>,
    in_lhs: bool,
}

impl<S,T,L,R> Parser<S,T> for AndThenParser<L,R> where L: Parser<S,T>, R: Parser<S,T>, S: for<'a> TypeWithLifetime<'a>, T: for<'a> TypeWithLifetime<'a>  {
    fn push_to<'a,D>(&mut self, value: At<'a,S>, downstream: &mut D) -> MatchResult<At<'a,S>> where D: Consumer<T> {
        if self.in_lhs {
            match self.lhs.push_to(value, downstream) {
                Undecided           => Undecided,
                Matched(Some(rest)) => { self.in_lhs = false; self.lhs.done_to(downstream); self.rhs.push_to(rest, downstream) },
                Matched(None)       => { self.in_lhs = false; self.lhs.done_to(downstream); Undecided },
                Failed(rest)        => Failed(rest),
            }
        } else {
            self.rhs.push_to(value, downstream)
        }
    }
    fn done_to<D>(&mut self, downstream: &mut D) -> bool where D: Consumer<T> {
        if self.in_lhs {
            self.lhs.done_to(downstream) && self.rhs.done_to(downstream)
        } else {
            self.in_lhs = true;
            self.rhs.done_to(downstream)
        }
    }
}

// ----------- Choice ---------------

#[derive(Clone, Debug)]
pub struct OrElseParser<L,R> {
    lhs: L,
    rhs: R,
    in_lhs: bool,
}

impl<S,T,L,R> Parser<S,T> for OrElseParser<L,R> where L: Parser<S,T>, R: Parser<S,T>, S: for<'a> TypeWithLifetime<'a>, T: for<'a> TypeWithLifetime<'a>  {
    fn push_to<'a,D>(&mut self, value: At<'a,S>, downstream: &mut D) -> MatchResult<At<'a,S>> where D: Consumer<T> {
        if self.in_lhs {
            match self.lhs.push_to(value, downstream) {
                Failed(Some(rest)) => { self.in_lhs = false; self.lhs.done_to(downstream); self.rhs.push_to(rest, downstream) },
                result             => result,
            }
        } else {
            self.rhs.push_to(value, downstream)
        }
    }
    fn done_to<D>(&mut self, downstream: &mut D) -> bool where D: Consumer<T> {
        if self.in_lhs {
            self.lhs.done_to(downstream)
        } else {
            self.in_lhs = true;
            self.rhs.done_to(downstream)
        }
    }
}

// ----------- Kleene star ---------------

#[derive(Clone, Debug)]
pub struct StarParser<P> {
    parser: P,
    matched: bool,
    first_time: bool,
}

impl<S,T,P> Parser<S,T> for StarParser<P> where P: Parser<S,T>, S: for<'a> TypeWithLifetime<'a>, T: for<'a> TypeWithLifetime<'a> {
    fn push_to<'a,D>(&mut self, mut value: At<'a,S>, downstream: &mut D) -> MatchResult<At<'a,S>> where D: Consumer<T> {
        loop {
            match self.parser.push_to(value, downstream) {
                Undecided           => { self.matched = false; return Undecided },
                Matched(Some(rest)) => { self.matched = true; self.first_time = false; self.parser.done_to(downstream); value = rest; },
                Matched(None)       => { self.matched = true; self.first_time = false; self.parser.done_to(downstream); return Undecided; },
                Failed(Some(rest))  => { self.matched = false; return Matched(Some(rest)) },
                Failed(None)        => { self.matched = false; return Failed(None) },
            }
        }
    }
    fn done_to<D>(&mut self, downstream: &mut D) -> bool where D: Consumer<T> {
        self.first_time = true;
        self.parser.done_to(downstream) | self.matched
    }
}


// ----------- Matching strings -------------

pub struct Str;

impl<'a> TypeWithLifetime<'a> for Str {
    type Type = &'a str;
}

// ----------- Constant parsers -------------

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum ConstantParserState {
    AtOffset(usize),
    AtEndMatched(bool),
    AtEndFailed(bool),
}

#[derive(Clone, Debug)]
pub struct ConstantParser {
    constant: String,
    state: ConstantParserState,
}

impl Parser<Str,Unit> for ConstantParser {
    fn push_to<'a,D>(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> where D: Consumer<Unit> {
        match self.state {
            AtOffset(index) if string == &self.constant[index..]           => { downstream.accept(()); self.state = AtEndMatched(true); Matched(None) },
            AtOffset(index) if string.starts_with(&self.constant[index..]) => { downstream.accept(()); self.state = AtEndMatched(false); Matched(Some(&string[(self.constant.len() - index)..])) },
            AtOffset(index) if self.constant[index..].starts_with(string)  => { self.state = AtOffset(index + string.len()); Undecided },
            AtOffset(0)     if !string.starts_with(&self.constant[..1])    => { self.state = AtEndFailed(true); Failed(Some(string)) },
            AtOffset(_)                                                    => { self.state = AtEndFailed(false); Failed(None) },
            AtEndMatched(_)                                                => { self.state = AtEndMatched(false); Matched(Some(string)) },
            AtEndFailed(true)                                              => { Failed(Some(string)) },
            AtEndFailed(false)                                             => { Failed(None) },
        }
    }
    fn done_to<D>(&mut self, _: &mut D) -> bool where D: Consumer<Unit> {
        let result = self.state == AtEndMatched(true);
        self.state = AtOffset(0);
        result
    }
}

pub fn constant(string: String) -> ConstantParser {
    ConstantParser{ constant: string, state: AtOffset(0) }
}

// If m is a Parser<Str,Unit> then m.buffer() is a Parser<Str,Str>.
// It does as little buffering as it can, but it does allocate as buffer for the case
// where the boundary marker of the input is misaligned with that of the parser.
// For example, m is matching string literals, and the input is '"abc' followed by 'def"'
// we have to buffer up '"abc'.

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
enum BufferedParserState {
    Beginning,
    Middle(String),
    EndMatch,
    EndFail(bool),
}

#[derive(Clone, Debug)]
pub struct BufferedParser<P> {
    parser: P,
    state: BufferedParserState,
}

impl<P> Parser<Str,Str> for BufferedParser<P> where P: Parser<Str,Unit> {
    fn push_to<'a,D>(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> where D: Consumer<Str> {
        match mem::replace(&mut self.state, EndMatch) {
            Beginning => {
                let result = self.parser.push(string);
                match result {
                    Undecided           => self.state = Middle(String::from(string)),
                    Failed(Some(_))     => self.state = EndFail(true),
                    Failed(None)        => self.state = EndFail(false),
                    Matched(Some(rest)) => downstream.accept(&string[..(string.len()-rest.len())]),
                    Matched(None)       => downstream.accept(string),
                }
                result
            },
            Middle(mut buffer) => {
                let result = self.parser.push(string);
                match result {
                    Undecided           => { buffer.push_str(string); self.state = Middle(buffer); },
                    Failed(Some(_))     => { self.state = EndFail(true) },
                    Failed(None)        => { self.state = EndFail(false) },
                    Matched(Some(rest)) => { buffer.push_str(&string[..(string.len()-rest.len())]); downstream.accept(&*buffer); },
                    Matched(None)       => { buffer.push_str(string); downstream.accept(&*buffer); },
                }
                result
            }
            EndMatch => Matched(Some(string)),
            EndFail(true) => Failed(Some(string)),
            EndFail(false) => Failed(None),
        }
    }
    fn done_to<D>(&mut self, downstream: &mut D) -> bool where D: Consumer<Str> {
        let result = self.parser.done();
        if result { if let Middle(ref buffer) = self.state { downstream.accept(&*buffer) } }
        self.state = Beginning;
        result
    }
}

// ----------- Tests -------------

#[test]
fn test_constant() {
    let mut parser = constant(String::from("abc"));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("alice"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcdef"), Matched(Some("def")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abc"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("a"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("cd"), Matched(Some("d")));
    assert_eq!(parser.done(), false);
}

#[test]
fn test_and_then() {
    let mut parser = constant(String::from("abc")).and_then(constant(String::from("def")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("alice"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abc"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcd"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcfred"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcdef"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("abcdefghi"), Matched(Some("ghi")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("a"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("cd"), Undecided);
    assert_eq!(parser.push("efg"), Matched(Some("g")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("cd"), Undecided);
    assert_eq!(parser.push("ef"), Matched(None));
    assert_eq!(parser.done(), true);
}

#[test]
fn test_or_else() {
    let mut parser = constant(String::from("abc")).or_else(constant(String::from("def")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("alice"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcdef"), Matched(Some("def")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abc"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("a"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("cd"), Matched(Some("d")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("dave"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("defghi"), Matched(Some("ghi")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("def"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("d"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("de"), Undecided);
    assert_eq!(parser.push("fg"), Matched(Some("g")));
    assert_eq!(parser.done(), false);
}

#[test]
fn test_star() {
    let mut parser = constant(String::from("abc")).star();
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("fred"), Matched(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("alice"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abc"), Undecided);
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("abca"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcfred"), Matched(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcabc"), Undecided);
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("abcabcghi"), Matched(Some("ghi")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("a"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("ca"), Undecided);
    assert_eq!(parser.push("bcg"), Matched(Some("g")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("ca"), Undecided);
    assert_eq!(parser.push("bc"), Undecided);
    assert_eq!(parser.done(), true);
}
