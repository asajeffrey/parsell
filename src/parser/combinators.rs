use std::mem;

use self::WillOrMight::{Will,Might};
use self::BufferedParserState::{Beginning,Middle,End};
use self::MatchResult::{WillMatch, MightMatch, WontMatch, MatchedAll, MatchedSome};

// ----------- Types for matching -------------

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

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum MatchResult<T> {
    WillMatch,
    MightMatch,
    WontMatch,
    MatchedAll,
    MatchedSome(T,T),
}

pub trait Matcher<T> where T: 'static+for<'a> TypeWithLifetime<'a> {
    // If push returns MightMatch or WontMatch, it is side-effect-free
    fn push<'a>(&mut self, value: At<'a,T>) -> MatchResult<At<'a,T>>;
    // Resets the matcher state back to its initial state
    fn done(&mut self);
}

// ----------- Types for parsers ------------

pub trait Consumer<T> where T: 'static+for<'a> TypeWithLifetime<'a> {
    fn accept<'a>(&mut self, arg: At<'a,T>);
}

pub trait Parser<S,T> where S: 'static+for<'a> TypeWithLifetime<'a>, T: 'static+for<'a> TypeWithLifetime<'a> {
    fn push<'a>(&mut self, value: At<'a,S>, downstream: &mut Consumer<T>) -> MatchResult<At<'a,S>>;
    fn done(&mut self, downstream: &mut Consumer<T>);
    // fn and_then<R: Parser<S,T>>(self, other: R) -> AndThenParser<Self,R> {
    //     AndThenParser{ lhs: self, rhs: other, in_lhs: true }
    // }
}

pub trait BufferableMatcher<S,T> where S: 'static+for<'a> TypeWithLifetime<'a>, T: Parser<S,S> {
    fn buffer(self) -> T;
}

// ----------- Sequencing ---------------

pub struct AndThenParser<L,R> {
    lhs: L,
    rhs: R,
    in_lhs: bool,
}

impl<S,T,L,R> Parser<S,T> for AndThenParser<L,R> where L: Parser<S,T>, R: Parser<S,T>, S: 'static+for<'a> TypeWithLifetime<'a>, T: 'static+for<'a> TypeWithLifetime<'a>  {
    fn push<'a>(&mut self, value: At<'a,S>, downstream: &mut Consumer<T>) -> MatchResult<At<'a,S>> {
        if self.in_lhs {
            match self.lhs.push(value, downstream) {
                WillMatch => MightMatch, // TODO: we are returning MightMatch even though lhs may have side-effects
                MightMatch => MightMatch,
                WontMatch => WontMatch,
                MatchedAll => { self.in_lhs = false; MightMatch },
                MatchedSome(_,rest) => { self.in_lhs = false; self.rhs.push(rest, downstream) } // TODO: if this returns MatchedSome(matched,rest) then this is the wrong matched
            }
        } else {
            self.rhs.push(value, downstream)
        }
    }
    fn done(&mut self, downstream: &mut Consumer<T>) {
        self.lhs.done(downstream);
        self.rhs.done(downstream);
        self.in_lhs = true;
    }
}

// ----------- Matching strings -------------

pub struct Str;

impl<'a> TypeWithLifetime<'a> for Str {
    type Type = &'a str;
}

// ----------- Constant parsers -------------

pub struct ConstantParser {
    constant: String,
    offset: Option<usize>,
}

impl Parser<Str,Unit> for ConstantParser {
    fn push<'a>(&mut self, string: &'a str, downstream: &mut Consumer<Unit>) -> MatchResult<&'a str> {
        match self.offset.take() {
            None => MatchedSome("",string),
            Some(index) if string == &self.constant[index..]           => { downstream.accept(()); MatchedAll },
            Some(index) if string.starts_with(&self.constant[index..]) => { downstream.accept(()); MatchedSome(&string[..index],&string[index..]) },
            Some(index) if self.constant[index..].starts_with(string)  => { self.offset = Some(index + string.len()); MightMatch },
            Some(_)                                                    => { WontMatch },
        }
    }
    fn done(&mut self, _: &mut Consumer<Unit>) {
        self.offset = Some(0);
    }
}

pub fn constant(string: String) -> ConstantParser {
    ConstantParser{ constant: string, offset: Some(0) }
}

// If m is a Matcher<Str> then m.buffer() is a Parser<Str,Str>.
// It does as little buffering as it can, but it does allocate as buffer for the case
// where the boundary marker of the input is misaligned with that of the matcher.
// For example, m is matching string literals, and the input is '"abc' followed by 'def"'
// we have to buffer up '"abc'.

enum WillOrMight {
    Will,
    Might,
}

enum BufferedParserState {
    Beginning,
    Middle(String,WillOrMight),
    End,
}

pub struct BufferedParser<S> {
    matcher: S,
    state: BufferedParserState,
}

impl<S> Parser<Str,Str> for BufferedParser<S> where S: Matcher<Str> {
    fn push<'a>(&mut self, string: &'a str, downstream: &mut Consumer<Str>) -> MatchResult<&'a str> {
        match mem::replace(&mut self.state, End) {
            Beginning => {
                let result = self.matcher.push(string);
                match result {
                    WillMatch               => self.state = Middle(String::from(string), Will),
                    MightMatch              => self.state = Middle(String::from(string), Might),
                    WontMatch               => (),
                    MatchedAll              => downstream.accept(string),
                    MatchedSome(matched, _) => downstream.accept(matched),
                }
                result
            },
            Middle(mut buffer, _) => {
                let result = self.matcher.push(string);
                match result {
                    WillMatch               => { buffer.push_str(string); self.state = Middle(buffer, Will); },
                    MightMatch              => { buffer.push_str(string); self.state = Middle(buffer, Might); },
                    WontMatch               => (),
                    MatchedAll              => { buffer.push_str(string); downstream.accept(&*buffer); },
                    MatchedSome(matched, _) => { buffer.push_str(matched); downstream.accept(&*buffer); },
                }
                result
            }
            End => MatchedSome("",string),
        }
    }
    fn done(&mut self, downstream: &mut Consumer<Str>) {
        match mem::replace(&mut self.state, Beginning) {
            Middle(buffer, Will) => downstream.accept(&*buffer),
            _                    => (),
        }
    }
}

impl<S> BufferableMatcher<Str,BufferedParser<S>> for S where S: Matcher<Str> {
    fn buffer(self) -> BufferedParser<S> {
        BufferedParser{ matcher: self, state: Beginning }
    }
}
