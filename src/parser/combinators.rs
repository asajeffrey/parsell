use std::mem;

use self::BufferedParserState::{Beginning, Middle, EndMatch, EndFail};
use self::MatchResult::{Undecided, Matched, Failed};
use self::StringParserState::{AtOffset, AtEndMatched, AtEndFailed};

// ----------- Types for consumers ------------

pub trait Consumer<T> {
    fn accept(&mut self, arg: T);
}

pub struct DiscardConsumer;

impl<T> Consumer<T> for DiscardConsumer {
    fn accept(&mut self, _: T) {}
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

pub trait ParseTo<S,D>: Parser<S> {
    // If push_to returns Failed(Some(s)), it is side-effect-free
    // push_to should be called with non-empty input,
    // when it returns Matched(Some(s)) or Failed(Some(s)) then s is non-empty.
    // In the case where T is "list-like" (e.g. &str or &[T])
    // push_to(a ++ b, d) is the same as push_to(a,d); push_to(b,d)
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S>;
    // Resets the parser state back to its initial state
    // Returns true if there was a match.
    fn done_to(&mut self, downstream: &mut D) -> bool;
}

// Helper methods
pub trait Parser<S> {
    fn push(&mut self, value: S) -> MatchResult<S> where Self: ParseTo<S,DiscardConsumer> {
        self.push_to(value, &mut DiscardConsumer)
    }
    fn done(&mut self) -> bool where Self: ParseTo<S,DiscardConsumer> {
        self.done_to(&mut DiscardConsumer)
    }
    fn and_then<R>(self, other: R) -> AndThenParser<Self,R> where Self: Sized, R: Parser<S> {
        AndThenParser{ lhs: self, rhs: CommittedParser{ parser: other }, in_lhs: true }
    }
    fn or_else<R>(self, other: R) -> OrElseParser<Self,R> where Self: Sized, R: Parser<S> {
        OrElseParser{ lhs: self, rhs: other, in_lhs: true }
    }
    fn star(self) -> StarParser<Self> where Self: Sized {
        StarParser{ parser: self, matched: true, first_time: true }
    }
    fn plus(self) -> PlusParser<Self> where Self: Sized {
        PlusParser{ parser: self, matched: false, first_time: true }
    }
    fn map<T,U,F>(self, function: F) -> MapParser<F,Self> where F: Fn(T) -> U, Self: Sized {
        MapParser{ function: function, parser: self }
    }
    fn emit<T>(self, value: T) -> EmitParser<T,Self> where T: Clone, Self: Sized {
        EmitParser{ value: value, parser: self }
    }
    fn filter<T,F>(self, function: F) -> FilterParser<F,Self> where F: Fn(T) -> bool, T: Copy, Self: Sized {
        FilterParser{ function: function, parser: self }
    }
}

pub trait StrParser<'a>: ParseTo<&'a str,DiscardConsumer> {
    fn buffer(self) -> BufferedParser<Self> where Self: Sized {
        BufferedParser{ parser: self, state: Beginning }
    }
}

impl<'a,P> StrParser<'a> for P where P: ParseTo<&'a str,DiscardConsumer> {}

// ----------- Map ---------------

#[derive(Debug)]
pub struct MapConsumer<'a,F:'a,C:'a> {
    function: &'a F,
    consumer: &'a mut C
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<'a,T,F,C> Consumer<T> for MapConsumer<'a,F,C>
where F: Fn<(T,)>, C: Consumer<<F as FnOnce<(T,)>>::Output> {
    fn accept(&mut self, arg: T) {
        self.consumer.accept((self.function)(arg));
    }
}

#[derive(Clone, Debug)]
pub struct MapParser<F,P> {
    function: F,
    parser: P
}

impl<S,F,P> Parser<S> for MapParser<F,P> where P: Parser<S> {}
impl<S,D,F,P> ParseTo<S,D> for MapParser<F,P> where P: for<'a> ParseTo<S,MapConsumer<'a,F,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let mut downstream = MapConsumer{ function: &mut self.function, consumer: downstream };
        self.parser.push_to(value, &mut downstream)
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let mut downstream = MapConsumer{ function: &mut self.function, consumer: downstream };
        self.parser.done_to(&mut downstream)
    }
}

// ----------- Emit ---------------

#[derive(Debug)]
pub struct EmitConsumer<'a,T:'a,C:'a> {
    value: &'a T,
    consumer: &'a mut C
}

impl<'a,T,C> Consumer<()> for EmitConsumer<'a,T,C> where C: Consumer<T>, T: Clone {
    fn accept(&mut self, _: ()) {
        self.consumer.accept(self.value.clone());
    }
}

#[derive(Clone, Debug)]
pub struct EmitParser<T,P> {
    pub value: T,
    pub parser: P
}

impl<S,T,P> Parser<S> for EmitParser<T,P> where P: Parser<S> {}
impl<S,D,T,P> ParseTo<S,D> for EmitParser<T,P> where T: Clone, P: for<'a> ParseTo<S,EmitConsumer<'a,T,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let mut downstream = EmitConsumer{ value: &self.value, consumer: downstream };
        self.parser.push_to(value, &mut downstream)
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let mut downstream = EmitConsumer{ value: &self.value, consumer: downstream };
        self.parser.done_to(&mut downstream)
    }
}

// ----------- Filter ---------------

#[derive(Debug)]
pub struct FilterConsumer<'a,F,C> where F: 'a, C: 'a {
    function: &'a F,
    consumer: &'a mut C
}

impl<'a,T,F,C> Consumer<T> for FilterConsumer<'a,F,C> where F: Fn(T) -> bool, T: Copy, C: Consumer<T> {
    fn accept(&mut self, arg: T) {
        if (self.function)(arg) {
            self.consumer.accept(arg)
        }
    }
}

#[derive(Clone, Debug)]
pub struct FilterParser<F,P> {
    function: F,
    parser: P
}

impl<S,F,P> Parser<S> for FilterParser<F,P> where P: Parser<S> {}
impl<S,D,F,P> ParseTo<S,D> for FilterParser<F,P> where P: for<'a> ParseTo<S,FilterConsumer<'a,F,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let mut downstream = FilterConsumer{ function: &mut self.function, consumer: downstream };
        self.parser.push_to(value, &mut downstream)
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let mut downstream = FilterConsumer{ function: &mut self.function, consumer: downstream };
        self.parser.done_to(&mut downstream)
    }
}

// ----------- Always commit ---------------

#[derive(Clone, Debug)]
pub struct CommittedParser<P> {
    parser: P,
}

impl<S,P> Parser<S> for CommittedParser<P> where P: Parser<S> {}
impl<S,D,P> ParseTo<S,D> for CommittedParser<P> where P: ParseTo<S,D> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        match self.parser.push_to(value, downstream) {
            Undecided     => Undecided,
            Matched(rest) => Matched(rest),
            Failed(_)     => Failed(None),
        }
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
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

impl<S,L,R> Parser<S> for AndThenParser<L,R> where L: Parser<S>, R: Parser<S> {}
impl<S,D,L,R> ParseTo<S,D> for AndThenParser<L,R> where L: ParseTo<S,D>, R: ParseTo<S,D> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
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
    fn done_to(&mut self, downstream: &mut D) -> bool {
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

impl<S,L,R> Parser<S> for OrElseParser<L,R> where L: Parser<S>, R: Parser<S> {}
impl<S,D,L,R> ParseTo<S,D> for OrElseParser<L,R> where L: ParseTo<S,D>, R: ParseTo<S,D> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        if self.in_lhs {
            match self.lhs.push_to(value, downstream) {
                Failed(Some(rest)) => { self.in_lhs = false; self.lhs.done_to(downstream); self.rhs.push_to(rest, downstream) },
                result             => result,
            }
        } else {
            self.rhs.push_to(value, downstream)
        }
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
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

impl<S,P> Parser<S> for StarParser<P> where P: Parser<S> {}
impl<S,D,P> ParseTo<S,D> for StarParser<P> where P: ParseTo<S,D> {
    fn push_to(&mut self, mut value: S, downstream: &mut D) -> MatchResult<S> {
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
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let result = self.parser.done_to(downstream) | self.matched;
        self.first_time = true;
        self.matched = true;
        result
    }
}

#[derive(Clone, Debug)]
pub struct PlusParser<P> {
    parser: P,
    matched: bool,
    first_time: bool,
}

impl<S,P> Parser<S> for PlusParser<P> where P: Parser<S> {}
impl<S,D,P> ParseTo<S,D> for PlusParser<P> where P: ParseTo<S,D> {
    fn push_to(&mut self, mut value: S, downstream: &mut D) -> MatchResult<S> {
        loop {
            match self.parser.push_to(value, downstream) {
                Undecided           => { self.matched = false; return Undecided },
                Matched(Some(rest)) => { self.matched = true; self.first_time = false; self.parser.done_to(downstream); value = rest; },
                Matched(None)       => { self.matched = true; self.first_time = false; self.parser.done_to(downstream); return Undecided; },
                Failed(Some(rest))  => { self.matched = false; return if self.first_time { Failed(Some(rest)) } else { Matched(Some(rest)) } },
                Failed(None)        => { self.matched = false; return Failed(None) },
            }
        }
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let result = self.parser.done_to(downstream) | self.matched;
        self.first_time = true;
        self.matched = false;
        result
    }
}

// ----------- Matching strings -------------

impl<'a> Consumer<&'a str> for String {
    fn accept(&mut self, arg: &'a str) {
        self.push_str(arg);
    }
}

// ----------- Matching arrays -------------

impl<'a,T> Consumer<&'a[T]> for Vec<T> where T: Clone {
    fn accept(&mut self, arg: &'a[T]) {
        self.extend(arg.iter().cloned());
    }
}

// ----------- Constant parsers -------------

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum StringParserState {
    AtOffset(usize),
    AtEndMatched(bool),
    AtEndFailed(bool),
}

#[derive(Clone, Debug)]
pub struct StringParser {
    constant: String,
    state: StringParserState,
}

impl<'a> Parser<&'a str> for StringParser {}
impl<'a,D> ParseTo<&'a str,D> for StringParser where D: Consumer<()> {
    fn push_to(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> {
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
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtOffset(0);
        result
    }
}

pub fn string(constant: &str) -> StringParser {
    StringParser{ constant: String::from(constant), state: AtOffset(0) }
}

#[derive(Clone, Debug)]
pub struct CharParser<P> {
    pattern: P,
    state: StringParserState,
}

impl<'a,P> Parser<&'a str> for CharParser<P> where P: Fn(char) -> bool {}
impl<'a,D,P> ParseTo<&'a str,D> for CharParser<P> where P: Fn(char) -> bool, D: Consumer<()> {
    fn push_to(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> {
        let ch = string.chars().next().unwrap();
        let len = ch.len_utf8();
        match self.state {
            AtOffset(_) if string.len() == len && (self.pattern)(ch) => { downstream.accept(()); self.state = AtEndMatched(true); Matched(None) },
            AtOffset(_) if (self.pattern)(ch)                        => { downstream.accept(()); self.state = AtEndMatched(false); Matched(Some(&string[len..])) },
            AtOffset(_)                                              => { self.state = AtEndFailed(true); Failed(Some(string)) },
            AtEndMatched(_)                                          => { self.state = AtEndMatched(false); Matched(Some(string)) },
            AtEndFailed(_)                                           => { Failed(Some(string)) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtOffset(0);
        result
    }
}
pub fn character<P>(pattern: P) -> CharParser<P> {
    CharParser{ pattern: pattern, state: AtOffset(0) }
}

#[derive(Clone, Debug)]
pub struct TokenParser<P> {
    pattern: P,
    state: StringParserState,
}

impl<'a,T,P> Parser<&'a[T]> for TokenParser<P> where P: Fn(T) -> bool {}
impl<'a,D,T,P> ParseTo<&'a[T],D> for TokenParser<P> where P: Fn(T) -> bool, D: Consumer<()>, T: Copy {
    fn push_to(&mut self, tokens: &'a[T], downstream: &mut D) -> MatchResult<&'a[T]> {
        let token = *tokens.first().unwrap();
        match self.state {
            AtOffset(_) if tokens.len() == 1 && (self.pattern)(token) => { downstream.accept(()); self.state = AtEndMatched(true); Matched(None) },
            AtOffset(_) if (self.pattern)(token)                      => { downstream.accept(()); self.state = AtEndMatched(false); Matched(Some(&tokens[1..])) },
            AtOffset(_)                                               => { self.state = AtEndFailed(true); Failed(Some(tokens)) },
            AtEndMatched(_)                                           => { self.state = AtEndMatched(false); Matched(Some(tokens)) },
            AtEndFailed(_)                                            => { Failed(Some(tokens)) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtOffset(0);
        result
    }
}

pub fn token<P>(pattern: P) -> TokenParser<P> {
    TokenParser{ pattern: pattern, state: AtOffset(0) }
}

#[derive(Clone, Debug)]
pub struct TokensParser<U> {
    constant: Vec<U>,
    state: StringParserState,
}

impl<'a,T,U> Parser<&'a[T]> for TokensParser<U> where T: PartialEq<U> {}
impl<'a,T,D,U> ParseTo<&'a[T],D> for TokensParser<U> where T: PartialEq<U>, D: Consumer<()> {
    fn push_to(&mut self, tokens: &'a[T], downstream: &mut D) -> MatchResult<&'a[T]> {
        match self.state {
            AtOffset(index) if eq_slice(tokens, &self.constant[index..])  => { downstream.accept(()); self.state = AtEndMatched(true); Matched(None) },
            AtOffset(index) if geq_slice(tokens, &self.constant[index..]) => { downstream.accept(()); self.state = AtEndMatched(false); Matched(Some(&tokens[(self.constant.len() - index)..])) },
            AtOffset(index) if leq_slice(tokens, &self.constant[index..]) => { self.state = AtOffset(index + tokens.len()); Undecided },
            AtOffset(0)     if geq_slice(tokens, &self.constant[..1])     => { self.state = AtEndFailed(true); Failed(Some(tokens)) },
            AtOffset(_)                                                   => { self.state = AtEndFailed(false); Failed(None) },
            AtEndMatched(_)                                               => { self.state = AtEndMatched(false); Matched(Some(tokens)) },
            AtEndFailed(true)                                             => { Failed(Some(tokens)) },
            AtEndFailed(false)                                            => { Failed(None) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtOffset(0);
        result
    }
}

pub fn eq_slice<'b,T,U>(xs: &'b[T], ys: &'b[U]) -> bool where T: PartialEq<U> {
    if xs.len() != ys.len() { return false; }
    for (x,y) in xs.iter().zip(ys.iter()) { if x != y { return false; } }
    true
}

pub fn leq_slice<'b,T,U>(xs: &'b[T], ys: &'b[U]) -> bool where T: PartialEq<U> {
    if xs.len() > ys.len() { return false; }
    for (x,y) in xs.iter().zip(ys.iter()) { if x != y { return false; } }
    true
}

pub fn geq_slice<'b,T,U>(xs: &'b[T], ys: &'b[U]) -> bool where T: PartialEq<U> {
    if xs.len() < ys.len() { return false; }
    for (x,y) in xs.iter().zip(ys.iter()) { if x != y { return false; } }
    true
}

pub fn tokens<U>(constant: Vec<U>) -> TokensParser<U> {
    TokensParser{ constant: constant, state: AtOffset(0) }
}

// If m is a ParseTo<&'a str, DiscardConsumer> then
// m.buffer() is a ParseTo<&'a str, C: Consumer<&str>>.
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

impl<'a,P> Parser<&'a str> for BufferedParser<P> where P: Parser<&'a str> {}
impl<'a,P,D> ParseTo<&'a str,D> for BufferedParser<P> where P: ParseTo<&'a str,DiscardConsumer>, D: for<'b> Consumer<&'b str> {
    fn push_to(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> {
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
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let result = self.parser.done();
        if result { if let Middle(ref buffer) = self.state { downstream.accept(&*buffer) } }
        self.state = Beginning;
        result
    }
}

// ----------- Tests -------------

#[test]
fn test_string() {
    let mut parser = string("abc");
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
    assert_eq!(parser.push("ab"), Failed(Some("ab")));
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
fn test_character() {
    let mut parser = character(char::is_alphabetic);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("99"), Failed(Some("99")));
    assert_eq!(parser.push("ab"), Failed(Some("ab")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcdef"), Matched(Some("bcdef")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("a"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("ab"), Matched(Some("b")));
    assert_eq!(parser.push("cd"), Matched(Some("cd")));
    assert_eq!(parser.done(), false);
}

#[test]
fn test_and_then() {
    let mut parser = string("abc").and_then(string("def"));
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
    let mut parser = string("abc").or_else(string("def"));
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
    let mut parser = string("abc").star();
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
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.push("ca"), Undecided);
    assert_eq!(parser.push("bc"), Undecided);
    assert_eq!(parser.done(), true);
}

#[test]
fn test_plus() {
    let mut parser = string("abc").plus();
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
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
    assert_eq!(parser.done(), false);
}

#[test]
fn test_map() {
    let mut parser = string("abc").map(|_| "hello");
    let mut result = String::new();
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("a", &mut result), Undecided);
    assert_eq!(result, "");
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("ab", &mut result), Undecided);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("cd", &mut result), Matched(Some("d")));
    assert_eq!(result, "hello");
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "hello");
    assert_eq!(parser.star().push_to("abcabcd", &mut result), Matched(Some("d")));
    assert_eq!(result, "hellohellohello");    
}

#[test]
fn test_buffer() {
    let mut parser = string("abc").buffer();
    let mut result = String::new();
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("a", &mut result), Undecided);
    assert_eq!(result, "");
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("ab", &mut result), Undecided);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("cd", &mut result), Matched(Some("d")));
    assert_eq!(result, "abc");
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "abc");
    assert_eq!(parser.star().push_to("abcabcd", &mut result), Matched(Some("d")));
    assert_eq!(result, "abcabcabc");    
}

#[test]
fn test_different_lifetimes() {
    fn go<'a,'b>(ab: &'a str, cd: &'b str) {
        fn tail(x:&str) -> &str { &x[1..] }
        let mut parser = string("abc").buffer().map(tail);
        let mut result = String::new();
        assert_eq!(parser.push_to(ab, &mut result), Undecided);
        assert_eq!(result, "");
        assert_eq!(parser.push_to(cd, &mut result), Matched(Some("d")));
        assert_eq!(result, "bc");
    }
    go("ab","cd");        
}
