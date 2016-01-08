use std::mem;

use self::BufferedParserState::{Beginning, Middle, EndMatch, EndFail};
use self::MatchResult::{Undecided, Committed, Matched, Failed};
use self::ConstantParserState::{AtOffset, AtEnd};

// ----------- Types with lifetimes -------------

// Borrowing encoding of paramaterized types from
// https://github.com/rust-lang/rfcs/blob/master/text/0195-associated-items.md#encoding-higher-kinded-types

pub trait TypeWithLifetime<'a> {
    type Type;
}

pub type At<'a,T> where T: TypeWithLifetime<'a> = T::Type;

pub struct Always<T> (T);

impl<'a,T> TypeWithLifetime<'a> for Always<T> {
    type Type = T;
}

pub type Unit = Always<()>;

// ----------- Types for consumers ------------

pub trait Consumer<T> where T: 'static+for<'a> TypeWithLifetime<'a> {
    fn accept<'a>(&mut self, arg: At<'a,T>);
}

struct DiscardConsumer;

impl Consumer<Unit> for DiscardConsumer {
    fn accept(&mut self, _: ()) {}
}

// ----------- Types for parsers ------------

// State machine transitions are:
//
// init -Undecided->  init
// init -Committed->  committed
// init -Matched(s)-> matched
// init -Failed(b)->  failed(b)
//
// committed -Committed->     committed
// committed -Matched(s)->    matched
// committed -Failed(false)-> failed(false)
//
// matched -Matched(s)-> matched
//
// failed(b) -Failed(b)-> failed(b)
//
// The Failed(b) action carries a boolean indicating if backtracking is allowed.
// Note that there is no transition . -Committed-> . -Failed(true)-> . so
// once a parser has committed, we can clean up space associated with backtracking.

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum MatchResult<T> {
    Undecided,
    Committed,
    Matched(T),
    Failed(bool),
}

pub trait Parser<S,T> where S: 'static+for<'a> TypeWithLifetime<'a>, T: 'static+for<'a> TypeWithLifetime<'a> {
    // If push returns Undecided or Failed(true), it is side-effect-free
    // In the case where T is "list-like" (e.g. &str or &[T])
    // push(nil) is a no-op
    // push(a ++ b) is the same as push(a); push(b)
    fn push<'a>(&mut self, value: At<'a,S>, downstream: &mut Consumer<T>) -> MatchResult<At<'a,S>>;
    // Resets the parser state back to its initial state
    fn done(&mut self, downstream: &mut Consumer<T>);
}

pub trait BufferableMatcher<S,T> where S: 'static+for<'a> TypeWithLifetime<'a>, T: Parser<S,S> {
    fn buffer(self) -> T;
}

// ----------- Always commit ---------------

pub struct CommittedParser<P> {
    parser: P,
}

impl<S,T,P> Parser<S,T> for CommittedParser<P> where P: Parser<S,T>, S: 'static+for<'a> TypeWithLifetime<'a>, T: 'static+for<'a> TypeWithLifetime<'a>  {
    fn push<'a>(&mut self, value: At<'a,S>, downstream: &mut Consumer<T>) -> MatchResult<At<'a,S>> {
        match self.parser.push(value, downstream) {
            Undecided     => Committed,
            Committed     => Committed,
            Matched(rest) => Matched(rest),
            Failed(_)     => Failed(false),
        }
    }
    fn done(&mut self, downstream: &mut Consumer<T>) {
        self.parser.done(downstream)
    }
}

// ----------- Sequencing ---------------

pub struct AndThenParser<L,R> {
    lhs: L,
    rhs: CommittedParser<R>,
    in_lhs: bool,
}

impl<S,T,L,R> Parser<S,T> for AndThenParser<L,R> where L: Parser<S,T>, R: Parser<S,T>, S: 'static+for<'a> TypeWithLifetime<'a>, T: 'static+for<'a> TypeWithLifetime<'a>  {
    fn push<'a>(&mut self, value: At<'a,S>, downstream: &mut Consumer<T>) -> MatchResult<At<'a,S>> {
        if self.in_lhs {
            match self.lhs.push(value, downstream) {
                Undecided     => Undecided,
                Committed     => Committed,
                Matched(rest) => { self.in_lhs = false; self.rhs.push(rest, downstream) },
                Failed(b)     => Failed(b),
            }
        } else {
            self.rhs.push(value, downstream)
        }
    }
    fn done(&mut self, downstream: &mut Consumer<T>) {
        self.lhs.done(downstream);
        self.rhs.done(downstream)
    }
}

// ----------- Matching strings -------------

pub struct Str;

impl<'a> TypeWithLifetime<'a> for Str {
    type Type = &'a str;
}

// ----------- Constant parsers -------------

pub enum ConstantParserState {
    AtOffset(usize),
    AtEnd(bool),
}

pub struct ConstantParser {
    constant: String,
    state: ConstantParserState,
}

impl Parser<Str,Unit> for ConstantParser {
    fn push<'a>(&mut self, string: &'a str, downstream: &mut Consumer<Unit>) -> MatchResult<&'a str> {
        match self.state {
            AtOffset(index) if string == &self.constant[index..]           => { downstream.accept(()); self.state = AtEnd(true); Matched("") },
            AtOffset(index) if string.starts_with(&self.constant[index..]) => { downstream.accept(()); self.state = AtEnd(true); Matched(&string[index..]) },
            AtOffset(index) if self.constant[index..].starts_with(string)  => { self.state = AtOffset(index + string.len()); Undecided },
            AtOffset(_)                                                    => { self.state = AtEnd(false); Failed(true) },
            AtEnd(true)                                                    => { Matched(string) },            
            AtEnd(false)                                                   => { Failed(true) },
        }
    }
    fn done(&mut self, _: &mut Consumer<Unit>) {
        self.state = AtOffset(0);
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

enum BufferedParserState {
    Beginning,
    Middle(String),
    EndMatch,
    EndFail(bool),
}

pub struct BufferedParser<P> {
    parser: P,
    state: BufferedParserState,
}

impl<P> Parser<Str,Str> for BufferedParser<P> where P: Parser<Str,Unit> {
    fn push<'a>(&mut self, string: &'a str, downstream: &mut Consumer<Str>) -> MatchResult<&'a str> {
        match mem::replace(&mut self.state, EndMatch) {
            Beginning => {
                let result = self.parser.push(string, &mut DiscardConsumer);
                match result {
                    Undecided     => self.state = Middle(String::from(string)),
                    Committed     => self.state = Middle(String::from(string)),
                    Failed(b)     => self.state = EndFail(b),
                    Matched(rest) => downstream.accept(&string[..(string.len()-rest.len())]),
                }
                result
            },
            Middle(mut buffer) => {
                let result = self.parser.push(string, &mut DiscardConsumer);
                match result {
                    Undecided     => { buffer.push_str(string); self.state = Middle(buffer); },
                    Committed     => { buffer.push_str(string); self.state = Middle(buffer); },
                    Failed(b)     => { self.state = EndFail(b); },
                    Matched(rest) => { buffer.push_str(&string[..(string.len()-rest.len())]); downstream.accept(&*buffer); },
                }
                result
            }
            EndMatch => Matched(string),
            EndFail(b) => Failed(b),
        }
    }
    fn done(&mut self, downstream: &mut Consumer<Str>) {
        self.parser.done(&mut DiscardConsumer);
        match mem::replace(&mut self.state, Beginning) {
            Middle(buffer) => downstream.accept(&*buffer),
            _              => (),
        }
    }
}
