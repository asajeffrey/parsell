use std::mem;

use self::BufferedParserState::{Beginning, Middle, EndMatch, EndFail};
use self::MatchResult::{Undecided, Matched, Failed};
use self::ConstParserState::{AtBeginning, AtEndMatched, AtEndFailed};

// ----------- Types for consumers ------------

pub trait Consumer<T> {
    fn accept(&mut self, value: T);
}

pub trait ErrConsumer<E> {
    fn error(&mut self, err: E);
}

pub struct DiscardConsumer;

impl<T> Consumer<T> for DiscardConsumer {
    fn accept(&mut self, _: T) {}
}

impl<E> ErrConsumer<E> for DiscardConsumer {
    fn error(&mut self, _: E) {}
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
    fn zip<T,R>(self, other: R) -> ZipParser<Self,R,T> where Self: Sized, R: Parser<S> {
        ZipParser{ lhs: self, rhs: CommittedParser{ parser: other }, buffer: Vec::new(), in_lhs: true }
    }
    fn and_then<R>(self, other: R) -> AndThenParser<Self,R> where Self: Sized, R: Parser<S> {
        AndThenParser{ lhs: self, rhs: CommittedParser{ parser: other }, in_lhs: true }
    }
    fn or_else<R>(self, other: R) -> OrElseParser<Self,R> where Self: Sized, R: Parser<S> {
        OrElseParser{ lhs: self, rhs: other, in_lhs: true }
    }
    fn or_emit<T>(self, default: T) -> OrEmitParser<Self,T> where Self: Sized {
        OrEmitParser{ parser: self, default: default, at_beginning: true }
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
    fn results(self) -> ResultParser<Self> where Self: Sized {
        ResultParser{ parser: self }
    }
    fn filter<T,F>(self, function: F) -> FilterParser<F,Self> where F: Fn(T) -> bool, T: Copy, Self: Sized {
        FilterParser{ function: function, parser: self }
    }
    fn ignore(self) -> IgnoreParser<Self> where Self: Sized {
        IgnoreParser{ parser: self }
    }
    fn collect<T>(self, empty: T) -> CollectParser<Self,T> where T: Clone, Self: Sized {
        CollectParser{ parser: self, buffer: empty.clone(), empty: empty, buffering: true }
    }
    fn buffer(self) -> BufferedParser<Self> where Self: Sized {
        BufferedParser{ parser: self, state: Beginning }
    }
}

// ----------- Map ---------------

#[derive(Debug)]
pub struct MapConsumer<'a,F:'a,D:'a> {
    function: &'a F,
    downstream: &'a mut D
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<'a,T,F,D> Consumer<T> for MapConsumer<'a,F,D>
where F: Fn<(T,)>, D: Consumer<<F as FnOnce<(T,)>>::Output> {
    fn accept(&mut self, arg: T) {
        self.downstream.accept((self.function)(arg));
    }
}

impl<'a,E,F,D> ErrConsumer<E> for MapConsumer<'a,F,D>
where D: ErrConsumer<E> {
    fn error(&mut self, err: E) {
        self.downstream.error(err);
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MapParser<F,P> {
    function: F,
    parser: P
}

impl<S,F,P> Parser<S> for MapParser<F,P> where P: Parser<S> {}
impl<S,D,F,P> ParseTo<S,D> for MapParser<F,P> where P: for<'a> ParseTo<S,MapConsumer<'a,F,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let mut downstream = MapConsumer{ function: &mut self.function, downstream: downstream };
        self.parser.push_to(value, &mut downstream)
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let mut downstream = MapConsumer{ function: &mut self.function, downstream: downstream };
        self.parser.done_to(&mut downstream)
    }
}

// ----------- Send errors to an error consumer ---------------

#[derive(Debug)]
pub struct ResultConsumer<'a,D> where D: 'a {
    downstream: &'a mut D
}

impl<'a,D,T,E> Consumer<Result<T,E>> for ResultConsumer<'a,D>
where D: Consumer<T>+ErrConsumer<E> {
    fn accept(&mut self, value: Result<T,E>) {
        match value {
            Ok(value) => self.downstream.accept(value),
            Err(err) => self.downstream.error(err),
        }
    }
}

impl<'a,D,E> ErrConsumer<E> for ResultConsumer<'a,D>
where D: ErrConsumer<E> {
    fn error(&mut self, err: E) {
        self.downstream.error(err)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ResultParser<P> {
    parser: P
}

impl<S,P> Parser<S> for ResultParser<P> where P: Parser<S> {}
impl<S,D,P> ParseTo<S,D> for ResultParser<P> where P: for<'a> ParseTo<S,ResultConsumer<'a,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let mut downstream = ResultConsumer{ downstream: downstream };
        self.parser.push_to(value, &mut downstream)
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let mut downstream = ResultConsumer{ downstream: downstream };
        self.parser.done_to(&mut downstream)
    }
}

// ----------- Ignore ---------------

#[derive(Copy, Clone, Debug)]
pub struct IgnoreParser<P> {
    parser: P
}

impl<S,P> Parser<S> for IgnoreParser<P> where P: Parser<S> {}
impl<S,D,P> ParseTo<S,D> for IgnoreParser<P> where P: ParseTo<S,DiscardConsumer> {
    fn push_to(&mut self, value: S, _: &mut D) -> MatchResult<S> {
        self.parser.push_to(value, &mut DiscardConsumer)
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        self.parser.done_to(&mut DiscardConsumer)
    }
}

// ----------- Filter ---------------

#[derive(Debug)]
pub struct FilterConsumer<'a,F,D> where F: 'a, D: 'a {
    function: &'a F,
    downstream: &'a mut D
}

impl<'a,T,F,D> Consumer<T> for FilterConsumer<'a,F,D> where F: Fn(T) -> bool, T: Copy, D: Consumer<T> {
    fn accept(&mut self, arg: T) {
        if (self.function)(arg) {
            self.downstream.accept(arg)
        }
    }
}

impl<'a,E,F,D> ErrConsumer<E> for FilterConsumer<'a,F,D> where D: ErrConsumer<E> {
    fn error(&mut self, err: E) {
        self.downstream.error(err)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct FilterParser<F,P> {
    function: F,
    parser: P
}

impl<S,F,P> Parser<S> for FilterParser<F,P> where P: Parser<S> {}
impl<S,D,F,P> ParseTo<S,D> for FilterParser<F,P> where P: for<'a> ParseTo<S,FilterConsumer<'a,F,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let mut downstream = FilterConsumer{ function: &mut self.function, downstream: downstream };
        self.parser.push_to(value, &mut downstream)
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let mut downstream = FilterConsumer{ function: &mut self.function, downstream: downstream };
        self.parser.done_to(&mut downstream)
    }
}

// ----------- Always commit ---------------

#[derive(Copy, Clone, Debug)]
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

#[derive(Copy, Clone, Debug)]
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

// ----------- Sequencing with zipping ---------------

// If p produces output (v1,v2,...,vM) and q produces output (w1,w2,...,wN)
// then p.zip(q) produces output ((v1,w1),(v2,w1),...,(vL,wL)) where L = min(M,N).

#[derive(Clone, Debug)]
pub struct ZipParser<L,R,T> {
    lhs: L,
    rhs: CommittedParser<R>,
    buffer: Vec<T>,
    in_lhs: bool,
}

pub struct ZipLhsConsumer<'a,T:'a,D:'a> {
    buffer: &'a mut Vec<T>,
    downstream: &'a mut D,
}

pub struct ZipRhsConsumer<'a,T:'a,D:'a> {
    buffer: &'a mut Vec<T>,
    downstream: &'a mut D,
}

impl<'a,T,D> Consumer<T> for ZipLhsConsumer<'a,T,D> {
    fn accept(&mut self, lhs: T) {
        self.buffer.push(lhs);
    }
}

impl<'a,T,U,D> Consumer<U> for ZipRhsConsumer<'a,T,D> where D: Consumer<(T,U)> {
    fn accept(&mut self, rhs: U) {
        if let Some(lhs) = self.buffer.pop() {
            self.downstream.accept((lhs,rhs))
        }
    }
}

impl<'a,T,D,E> ErrConsumer<E> for ZipLhsConsumer<'a,T,D> where D: ErrConsumer<E> {
    fn error(&mut self, err: E) {
        self.downstream.error(err);
    }
}

impl<'a,T,D,E> ErrConsumer<E> for ZipRhsConsumer<'a,T,D> where D: ErrConsumer<E> {
    fn error(&mut self, err: E) {
        self.downstream.error(err);
    }
}

impl<S,T,L,R> Parser<S> for ZipParser<L,R,T> where L: Parser<S>, R: Parser<S> {}
impl<S,T,D,L,R> ParseTo<S,D> for ZipParser<L,R,T> where L: for<'a> ParseTo<S,ZipLhsConsumer<'a,T,D>>, R: for<'a> ParseTo<S,ZipRhsConsumer<'a,T,D>> {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        if self.in_lhs {
            match self.lhs.push_to(value, &mut ZipLhsConsumer{ buffer: &mut self.buffer, downstream: downstream }) {
                Undecided           => Undecided,
                Matched(Some(rest)) => { self.in_lhs = false; self.lhs.done_to(&mut ZipLhsConsumer{ buffer: &mut self.buffer, downstream: downstream }); self.buffer.reverse(); self.rhs.push_to(rest, &mut ZipRhsConsumer{ buffer: &mut self.buffer, downstream: downstream }) },
                Matched(None)       => { self.in_lhs = false; self.lhs.done_to(&mut ZipLhsConsumer{ buffer: &mut self.buffer, downstream: downstream }); self.buffer.reverse(); Undecided },
                Failed(rest)        => Failed(rest),
            }
        } else {
            self.rhs.push_to(value, &mut ZipRhsConsumer{ buffer: &mut self.buffer, downstream: downstream })
        }
    }
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let result = if self.in_lhs {
            self.lhs.done_to(&mut ZipLhsConsumer{ buffer: &mut self.buffer, downstream: downstream }) && { self.buffer.reverse(); self.rhs.done_to(&mut ZipRhsConsumer{ buffer: &mut self.buffer, downstream: downstream }) }
        } else {
            self.in_lhs = true;
            self.rhs.done_to(&mut ZipRhsConsumer{ buffer: &mut self.buffer, downstream: downstream })
        };
        self.buffer.clear();
        result
    }
}

// ----------- Choice ---------------

#[derive(Copy, Clone, Debug)]
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

#[derive(Copy, Clone, Debug)]
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
                Failed(Some(rest))  => { self.matched = false; return Matched(Some(rest)); },
                Failed(None)        => { self.matched = false; return Failed(None); },
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

#[derive(Copy, Clone, Debug)]
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

// ----------- Matching arrays -------------

impl<'a,T> Consumer<&'a[T]> for Vec<T> where T: Clone {
    fn accept(&mut self, arg: &'a[T]) {
        self.extend(arg.iter().cloned());
    }
}

impl<T> Consumer<T> for Vec<T> {
    fn accept(&mut self, x: T) { self.push(x); }
}

// // ----------- Constant parsers -------------

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum ConstParserState {
    AtBeginning,
    AtEndMatched(bool),
    AtEndFailed(bool),
}

#[derive(Copy, Clone, Debug)]
pub struct CharMatchParser<P> {
    pattern: P,
    state: ConstParserState,
}

impl<'a,P> Parser<&'a str> for CharMatchParser<P> where P: Fn(char) -> bool {}
impl<'a,D,P> ParseTo<&'a str,D> for CharMatchParser<P> where P: Fn(char) -> bool, D: Consumer<char> {
    fn push_to(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> {
        let ch = string.chars().next().unwrap();
        let len = ch.len_utf8();
        match self.state {
            AtBeginning if string.len() == len && (self.pattern)(ch) => { downstream.accept(ch); self.state = AtEndMatched(true); Matched(None) },
            AtBeginning if (self.pattern)(ch)                        => { downstream.accept(ch); self.state = AtEndMatched(false); Matched(Some(&string[len..])) },
            AtBeginning                                              => { self.state = AtEndFailed(true); Failed(Some(string)) },
            AtEndMatched(_)                                          => { self.state = AtEndMatched(false); Matched(Some(string)) },
            AtEndFailed(_)                                           => { Failed(Some(string)) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtBeginning;
        result
    }
}

pub fn character_match<P>(pattern: P) -> CharMatchParser<P> {
    CharMatchParser{ pattern: pattern, state: AtBeginning }
}

#[derive(Copy, Clone, Debug)]
pub struct CharParser {
    ch: char,
    state: ConstParserState,
}

impl<'a> Parser<&'a str> for CharParser {}
impl<'a,D> ParseTo<&'a str,D> for CharParser where D: Consumer<char> {
    fn push_to(&mut self, string: &'a str, downstream: &mut D) -> MatchResult<&'a str> {
        let ch = string.chars().next().unwrap();
        let len = ch.len_utf8();
        match self.state {
            AtBeginning if string.len() == len && self.ch == ch => { downstream.accept(ch); self.state = AtEndMatched(true); Matched(None) },
            AtBeginning if self.ch == ch                        => { downstream.accept(ch); self.state = AtEndMatched(false); Matched(Some(&string[len..])) },
            AtBeginning                                         => { self.state = AtEndFailed(true); Failed(Some(string)) },
            AtEndMatched(_)                                     => { self.state = AtEndMatched(false); Matched(Some(string)) },
            AtEndFailed(_)                                      => { Failed(Some(string)) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtBeginning;
        result
    }
}

pub fn character(ch: char) -> CharParser {
    CharParser{ ch: ch, state: AtBeginning }
}

#[derive(Copy, Clone, Debug)]
pub struct TokenMatchParser<P> {
    pattern: P,
    state: ConstParserState,
}

impl<'a,T,P> Parser<&'a[T]> for TokenMatchParser<P> where P: Fn(T) -> bool {}
impl<'a,D,T,P> ParseTo<&'a[T],D> for TokenMatchParser<P> where P: Fn(T) -> bool, D: Consumer<T>, T: Copy {
    fn push_to(&mut self, tokens: &'a[T], downstream: &mut D) -> MatchResult<&'a[T]> {
        let token = *tokens.first().unwrap();
        match self.state {
            AtBeginning if tokens.len() == 1 && (self.pattern)(token) => { downstream.accept(token); self.state = AtEndMatched(true); Matched(None) },
            AtBeginning if (self.pattern)(token)                      => { downstream.accept(token); self.state = AtEndMatched(false); Matched(Some(&tokens[1..])) },
            AtBeginning                                               => { self.state = AtEndFailed(true); Failed(Some(tokens)) },
            AtEndMatched(_)                                           => { self.state = AtEndMatched(false); Matched(Some(tokens)) },
            AtEndFailed(_)                                            => { Failed(Some(tokens)) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtBeginning;
        result
    }
}

pub fn token_match<P>(pattern: P) -> TokenMatchParser<P> {
    TokenMatchParser{ pattern: pattern, state: AtBeginning }
}

#[derive(Copy, Clone, Debug)]
pub struct TokenParser<U> {
    tok: U,
    state: ConstParserState,
}

impl<'a,T,U> Parser<&'a[T]> for TokenParser<U> where T: PartialEq<U> {}
impl<'a,D,T,U> ParseTo<&'a[T],D> for TokenParser<U> where D: Consumer<T>, T: Copy+PartialEq<U> {
    fn push_to(&mut self, tokens: &'a[T], downstream: &mut D) -> MatchResult<&'a[T]> {
        let tok = *tokens.first().unwrap();
        match self.state {
            AtBeginning if tokens.len() == 1 && tok == self.tok => { downstream.accept(tok); self.state = AtEndMatched(true); Matched(None) },
            AtBeginning if tok == self.tok                      => { downstream.accept(tok); self.state = AtEndMatched(false); Matched(Some(&tokens[1..])) },
            AtBeginning                                         => { self.state = AtEndFailed(true); Failed(Some(tokens)) },
            AtEndMatched(_)                                     => { self.state = AtEndMatched(false); Matched(Some(tokens)) },
            AtEndFailed(_)                                      => { Failed(Some(tokens)) },
        }
    }
    fn done_to(&mut self, _: &mut D) -> bool {
        let result = self.state == AtEndMatched(true);
        self.state = AtBeginning;
        result
    }
}

pub fn token<U>(tok: U) -> TokenParser<U> {
    TokenParser{ tok: tok, state: AtBeginning }
}

// Optional parser, with a default value

#[derive(Clone, Debug)]
pub struct OrEmitParser<P,T> {
    parser: P,
    default: T,
    at_beginning: bool,
}

impl<S,P,T> Parser<S> for OrEmitParser<P,T> where P: Parser<S> {}
impl<S,D,P,T> ParseTo<S,D> for OrEmitParser<P,T> where P: ParseTo<S,D>, D: Consumer<T>, T: Clone {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        if self.at_beginning {
            self.at_beginning = false;
            match self.parser.push_to(value, downstream) {
                Failed(Some(rest))  => { downstream.accept(self.default.clone()); Matched(Some(rest)) },
                result              => result,
            }
        } else {
            self.parser.push_to(value, downstream)
        }
    }    
    fn done_to(&mut self, downstream: &mut D) -> bool {
        if self.at_beginning {
            if !self.parser.done_to(downstream) { downstream.accept(self.default.clone()); }
            true
        } else {
            self.at_beginning = true;
            self.parser.done_to(downstream)
        }
    }
}

// Collect the output of a parser into a buffer

#[derive(Clone, Debug)]
pub struct CollectParser<P,T> {
    parser: P,
    buffer: T,
    empty: T,
    buffering: bool,
}

impl<S,P,T> Parser<S> for CollectParser<P,T> where P: Parser<S> {}
impl<S,D,P,T> ParseTo<S,D> for CollectParser<P,T> where P: ParseTo<S,T>, D: Consumer<T>, T: Clone {
    fn push_to(&mut self, value: S, downstream: &mut D) -> MatchResult<S> {
        let result = self.parser.push_to(value, &mut self.buffer);
        if self.buffering {
            if let Matched(_) = result {
                let buffer = mem::replace(&mut self.buffer, self.empty.clone());
                self.buffering = false;
                downstream.accept(buffer);
            }
        }
        result
    }    
    fn done_to(&mut self, downstream: &mut D) -> bool {
        let result = self.parser.done_to(&mut self.buffer);
        if self.buffering {
            let buffer = mem::replace(&mut self.buffer, self.empty.clone());
            if result { downstream.accept(buffer); }
        }
        self.buffering = true;    
        result
    }
}

// If m is a ParseTo<&'a str, DiscardConsumer> then
// m.buffer() is a ParseTo<&'a str, D, E> where D: Consumer<&str>.
// It does as little buffering as it can, but it does allocate as buffer for the case
// where the boundary marker of the input is misaligned with that of the parser.
// For example, m is matching string literals, and the input is '"abc' followed by 'def"'
// we have to buffer up '"abc'.

// TODO: at the moment, this is discarding errors

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
                let result = self.parser.push_to(string, &mut DiscardConsumer);
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
                let result = self.parser.push_to(string, &mut DiscardConsumer);
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
        let result = self.parser.done_to(&mut DiscardConsumer);
        if result { if let Middle(ref buffer) = self.state { downstream.accept(&*buffer) } }
        self.state = Beginning;
        result
    }
}

// ----------- Tests -------------

#[test]
fn test_character() {
    let mut parser = character_match(char::is_alphabetic);
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
    let mut parser = character('a').and_then(character('b')).and_then(character('c'));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("alice"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abc"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("abcd"), Matched(Some("d")));
    assert_eq!(parser.done(), false);
}

#[test]
fn test_zip() {
    let mut parser = character_match(char::is_alphabetic).star().zip(character_match(char::is_numeric).star());
    let mut results = Vec::new();
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, []);
    results.clear();
    assert_eq!(parser.push_to("a1", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, [('a','1')]);
    results.clear();
    assert_eq!(parser.push_to("ab12", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, [('a','1'),('b','2')]);
    results.clear();
    assert_eq!(parser.push_to("abc12", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, [('a','1'),('b','2')]);
    results.clear();
    assert_eq!(parser.push_to("ab123", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, [('a','1'),('b','2')]);
    results.clear();
}

#[test]
fn test_or_else() {
    let mut parser = character('a').and_then(character('b')).or_else(character('c').and_then(character('d')));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("fred"), Failed(Some("fred")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("alice"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("abcdef"), Matched(Some("cdef")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("ab"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("a"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("a"), Undecided);
    assert_eq!(parser.push("bc"), Matched(Some("c")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("charlie"), Failed(None));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("cde"), Matched(Some("e")));
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("cd"), Matched(None));
    assert_eq!(parser.done(), true);
    assert_eq!(parser.push("c"), Undecided);
    assert_eq!(parser.done(), false);
    assert_eq!(parser.push("c"), Undecided);
    assert_eq!(parser.push("de"), Matched(Some("e")));
    assert_eq!(parser.done(), false);
}

#[test]
fn test_star() {
    let mut parser = character('a').and_then(character('b')).and_then(character('c')).star();
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
    let mut parser = character('a').and_then(character('b')).and_then(character('c')).plus();
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
    let mut parser = character('a').and_then(character('b')).and_then(character('c')).map(|ch: char| ch.to_uppercase().collect::<String>());
    let mut result = String::new();
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "");
    assert_eq!(parser.push_to("a", &mut result), Undecided);
    assert_eq!(result, "A");
    assert_eq!(parser.push_to("b", &mut result), Undecided);
    assert_eq!(result, "AB");
    assert_eq!(parser.push_to("c", &mut result), Matched(None));
    assert_eq!(result, "ABC");
    assert_eq!(parser.done_to(&mut result), true);
    assert_eq!(result, "ABC");
}

#[test]
fn test_or_emit() {
    let mut parser = character('a').and_then(character('b')).and_then(character('c')).or_emit('z');
    let mut result = String::new();
    assert_eq!(parser.push_to("a", &mut result), Undecided);
    assert_eq!(result, "a");
    assert_eq!(parser.push_to("b", &mut result), Undecided);
    assert_eq!(result, "ab");
    assert_eq!(parser.push_to("c", &mut result), Matched(None));
    assert_eq!(result, "abc");
    assert_eq!(parser.done_to(&mut result), true);
    assert_eq!(result, "abc");
    result.clear();
    assert_eq!(parser.push_to("d", &mut result), Matched(Some("d")));
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "z");
    result.clear();
    assert_eq!(parser.push_to("ad", &mut result), Failed(None));
    assert_eq!(parser.done_to(&mut result), false);
    assert_eq!(result, "a");
    result.clear();
    assert_eq!(parser.done_to(&mut result), true);
    assert_eq!(result, "z");
}

#[test]
fn test_collect() {
    let mut parser = character_match(char::is_alphabetic).plus().and_then(character(';').ignore()).collect(String::new()).plus();
    let mut results: Vec<String> = Vec::new();
    assert_eq!(parser.done_to(&mut results), false);
    assert_eq!(results.len(), 0);
    results.clear();
    assert_eq!(parser.push_to("abc;", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, ["abc"]);
    results.clear();
    assert_eq!(parser.push_to("abc;de", &mut results), Undecided);
    assert_eq!(parser.push_to("f;", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), true);
    assert_eq!(results, ["abc","def"]);
    results.clear();
    assert_eq!(parser.push_to("abc;def;ghi", &mut results), Undecided);
    assert_eq!(parser.done_to(&mut results), false);
    assert_eq!(results, ["abc","def"]);
    results.clear();
    assert_eq!(parser.push_to("abc;def;.", &mut results), Matched(Some(".")));
    assert_eq!(parser.done_to(&mut results), false);
    assert_eq!(results, ["abc","def"]);
    results.clear();
}

#[test]
fn test_buffer() {
    let mut parser = character('a').and_then(character('b')).and_then(character('c')).buffer();
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
        let mut parser = character('a').and_then(character('b')).and_then(character('c')).buffer().map(tail);
        let mut result = String::new();
        assert_eq!(parser.push_to(ab, &mut result), Undecided);
        assert_eq!(result, "");
        assert_eq!(parser.push_to(cd, &mut result), Matched(Some("d")));
        assert_eq!(result, "bc");
    }
    go("ab","cd");        
}
