#![feature(unboxed_closures)]

extern crate core;

use self::GuardedParseResult::{Empty,Abort,Commit};
use self::ParseResult::{Done,Continue};
use self::OrElseParser::{Lhs,Rhs};
use self::OrEmitParser::{Unresolved,Resolved};
use self::AndThenParser::{InLhs,InRhs};
use self::Str::{Borrowed,Owned};

// ----------- Types for consumers ------------

pub trait Consumer<T> {
    fn push(&mut self, value: T);
}

pub struct DiscardConsumer;

impl<T> Consumer<T> for DiscardConsumer {
    fn push(&mut self, _: T) {}
}

impl Consumer<String> for String {
    fn push(&mut self, arg: String) {
        self.push_str(&*arg);
    }
}

impl<'a> Consumer<&'a str> for String {
    fn push(&mut self, arg: &'a str) {
        self.push_str(arg);
    }
}

impl Consumer<char> for String {
    fn push(&mut self, x: char) { self.push(x); }
}

impl<'a,T> Consumer<&'a[T]> for Vec<T> where T: Clone {
    fn push(&mut self, arg: &'a[T]) {
        self.extend(arg.iter().cloned());
    }
}

impl<T> Consumer<T> for Vec<T> {
    fn push(&mut self, x: T) { self.push(x); }
}

// ----------- Types data which can discard a suffix (e.g. strings, slices...) ------------

pub trait DropSuffix {
    fn drop_suffix(self, suffix: Self) -> Self;
}

impl<'a> DropSuffix for &'a str {
    fn drop_suffix(self, suffix: &'a str) -> &'a str {
        &self[0..(self.len() - suffix.len())]
    }
}

impl<'a,T> DropSuffix for &'a[T] {
    fn drop_suffix(self, suffix: &'a[T]) -> &'a[T] {
        &self[0..(self.len() - suffix.len())]
    }
}

// ----------- Types for parsers ------------

pub trait Parser {
    fn map<F>(self, f: F) -> MapParser<Self,F> where Self:Sized, { MapParser(self,f) }
}

pub trait ParserOf<S>: Parser {
    type Output;
    fn parse(self, value: S) -> ParseResult<Self,S> where Self: Sized;
    fn done(self) -> Self::Output where Self: Sized;
}

pub enum ParseResult<P,S> where P: ParserOf<S> {
    Done(S,P::Output),
    Continue(P),
}

pub trait GuardedParser {
    fn or_else<P>(self, other: P) -> OrElseGuardedParser<Self,P> where Self:Sized, P: GuardedParser { OrElseGuardedParser(self,other) }
    fn or_emit<F,R>(self, default: F) -> OrEmitParser<Self,F,R> where Self:Sized { Unresolved(self,default) }
    fn and_then<P>(self, other: P) -> AndThenGuardedParser<Self,P> where Self:Sized, P: Parser { AndThenGuardedParser(self,other) }
    fn plus<F>(self, factory: F) -> PlusParser<Self,F> where Self:Sized { PlusParser(self,factory) }
    fn star<B,R>(self, buffer: B) -> StarParser<Self,R,B> where Self:Sized { StarParser(self,None,buffer) }
    fn map<F>(self, f: F) -> MapGuardedParser<Self,F> where Self:Sized, { MapGuardedParser(self,f) }
    fn buffer(self) -> BufferedGuardedParser<Self> where Self:Sized, { BufferedGuardedParser(self) }
}

pub trait GuardedParserOf<S>: GuardedParser {
    type Rest: ParserOf<S>;
    fn parse(self, value: S) -> GuardedParseResult<Self,S> where Self: Sized;
}

pub enum GuardedParseResult<P,S> where P: GuardedParserOf<S> {
    Empty(P),
    Abort(S),
    Commit(ParseResult<P::Rest,S>),
}

// ----------- Map ---------------

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

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<P,F> Parser for MapParser<P,F> where P: Parser {}
impl<P,F,S,T> ParserOf<S> for MapParser<P,F> where P: ParserOf<S,Output=T>, F: Fn<(T,)> {
    type Output = F::Output;
    fn parse(self, value: S) -> ParseResult<Self,S> {
        match self.0.parse(value) {
            Done(rest,result) => Done(rest,(self.1)(result)),
            Continue(parsing) => Continue(MapParser(parsing,self.1)),
        }
    }
    fn done(self) -> Self::Output {
        (self.1)(self.0.done())
    }
}

#[derive(Debug)]
pub struct MapGuardedParser<P,F>(P,F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P,F> Copy for MapGuardedParser<P,F> where P: Copy, F: Copy {}
impl<P,F> Clone for MapGuardedParser<P,F> where P: Clone, F: Copy {
    fn clone(&self) -> Self {
        MapGuardedParser(self.0.clone(),self.1)
    }
}

impl<P,F> GuardedParser for MapGuardedParser<P,F> where P: GuardedParser {}
impl<P,F,S,Q,T> GuardedParserOf<S> for MapGuardedParser<P,F> where P: GuardedParserOf<S,Rest=Q>, Q: ParserOf<S,Output=T>, F: Fn<(T,)> {
    type Rest = MapParser<P::Rest,F>;
    fn parse(self, value: S) -> GuardedParseResult<Self,S> {
        match self.0.parse(value) {
            Empty(parser) => Empty(MapGuardedParser(parser,self.1)),
            Commit(Done(rest,result)) => Commit(Done(rest,(self.1)(result))),
            Commit(Continue(parsing)) => Commit(Continue(MapParser(parsing,self.1))),
            Abort(value) => Abort(value),
        }
    }
}

// ----------- Sequencing ---------------

#[derive(Copy, Clone, Debug)]
pub struct AndThenGuardedParser<P,Q>(P,Q);

impl<P,Q> GuardedParser for AndThenGuardedParser<P,Q> where P: GuardedParser, Q: Parser {}
impl<P,Q,R,S> GuardedParserOf<S> for AndThenGuardedParser<P,Q> where P: GuardedParserOf<S,Rest=R>, Q: ParserOf<S>, R: ParserOf<S> {
    type Rest = AndThenParser<R,Q,R::Output>;
    fn parse(self, value: S) -> GuardedParseResult<Self,S> {
        match self {
            AndThenGuardedParser(lhs,rhs) => {
                match lhs.parse(value) {
                    Empty(lhs) => Empty(AndThenGuardedParser(lhs,rhs)),
                    Commit(Done(rest,result1)) => match rhs.parse(rest) {
                        Done(rest,result2) => Commit(Done(rest,(result1,result2))),
                        Continue(parsing) => Commit(Continue(InRhs(result1,parsing))),
                    },
                    Commit(Continue(parsing)) => Commit(Continue(InLhs(parsing,rhs))),
                    Abort(value) => Abort(value),
                }
            },
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum AndThenParser<P,Q,T> {
    InLhs(P,Q),
    InRhs(T,Q),
}

impl<P,Q,T> Parser for AndThenParser<P,Q,T> where P: Parser, Q: Parser {}
impl<P,Q,T,U,S> ParserOf<S> for AndThenParser<P,Q,T> where P: ParserOf<S,Output=T>, Q: ParserOf<S,Output=U> {
    type Output = (T,U);
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

// ----------- Choice ---------------

#[derive(Copy, Clone, Debug)]
pub struct OrElseGuardedParser<P,Q>(P,Q);

impl<P,Q> GuardedParser for OrElseGuardedParser<P,Q> where P: GuardedParser, Q: GuardedParser {}
impl<P,Q,S,T> GuardedParserOf<S> for OrElseGuardedParser<P,Q> where P: GuardedParserOf<S>, Q: GuardedParserOf<S>, P::Rest: ParserOf<S,Output=T>, Q::Rest: ParserOf<S,Output=T> {
    type Rest = OrElseParser<P::Rest,Q::Rest>;
    fn parse(self, value: S) -> GuardedParseResult<Self,S> {
        match self.0.parse(value) {
            Empty(lhs) => Empty(OrElseGuardedParser(lhs,self.1)),
            Commit(Done(rest,result)) => Commit(Done(rest,result)),
            Commit(Continue(parsing)) => Commit(Continue(Lhs(parsing))),
            Abort(value) => match self.1.parse(value) {
                Empty(_) => panic!("lhs and rhs disagree about emptiness"),
                Commit(Done(rest,result)) => Commit(Done(rest,result)),
                Commit(Continue(parsing)) => Commit(Continue(Rhs(parsing))),
                Abort(value) => Abort(value),
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum OrElseParser<P,Q> {
    Lhs(P),
    Rhs(Q),
}

impl<P,Q> Parser for OrElseParser<P,Q> where P: Parser, Q: Parser {}
impl<P,Q,S,T> ParserOf<S> for OrElseParser<P,Q> where P: ParserOf<S,Output=T>, Q: ParserOf<S,Output=T> {
    type Output = T;
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
pub enum OrEmitParser<P,F,R> {
    Unresolved(P,F),
    Resolved(R),
}

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P,F,R> Copy for OrEmitParser<P,F,R> where P: Copy, F: Copy, R: Copy {}
impl<P,F,R> Clone for OrEmitParser<P,F,R> where P: Copy, F: Copy, R: Clone {
    fn clone(&self) -> Self {
        match *self {
            Unresolved(parser,default) => Unresolved(parser,default),
            Resolved(ref parser) => Resolved(parser.clone()),
        }
    }
}

impl<P,F,R> Parser for OrEmitParser<P,F,R> where P: GuardedParser, R: Parser {}
impl<P,F,R,S,T> ParserOf<S> for OrEmitParser<P,F,R> where P: GuardedParserOf<S,Rest=R>, R: ParserOf<S,Output=T>, F:Fn<(),Output=T> {
    type Output = T;
    fn parse(self, value: S) -> ParseResult<Self,S> {
        match self {
            Unresolved(parser,default) => {
                match parser.parse(value) {
                    Empty(parser) => Continue(Unresolved(parser,default)),
                    Commit(Done(rest,result)) => Done(rest,result),
                    Commit(Continue(parsing)) => Continue(Resolved(parsing)),
                    Abort(value) => Done(value,default()),
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
    fn done(self) -> T {
        match self {
            Unresolved(_,default) => default(),
            Resolved(parser) => parser.done(),
        }
    }
}

// ----------- Kleene star ---------------

#[derive(Clone,Debug)]
pub struct StarParser<P,Q,T>(P,Option<Q>,T);

impl<P,Q,T> Parser for StarParser<P,Q,T> where P: Copy+GuardedParser, Q: Parser {}
impl<P,Q,T,S> ParserOf<S> for StarParser<P,Q,T> where P: Copy+GuardedParserOf<S,Rest=Q>, Q: ParserOf<S>, T: Consumer<Q::Output> {
    type Output = T;
    fn parse(mut self, mut value: S) -> ParseResult<Self,S> {
        loop {
            match self.1.take() {
                None => match self.0.parse(value) {
                    Empty(_) => return Continue(StarParser(self.0,None,self.2)),
                    Commit(Continue(parsing)) => return Continue(StarParser(self.0,Some(parsing),self.2)),
                    Commit(Done(rest,result)) => { self.2.push(result); value = rest; },
                    Abort(rest) => return Done(rest,self.2),
                },
                Some(parser) => match parser.parse(value) {
                    Continue(parsing) => return Continue(StarParser(self.0,Some(parsing),self.2)),
                    Done(rest,result) => { self.2.push(result); value = rest; },
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

impl<P,F> GuardedParser for PlusParser<P,F> where P: Copy+GuardedParser {}
impl<P,F,Q,S> GuardedParserOf<S> for PlusParser<P,F> where P: Copy+GuardedParserOf<S,Rest=Q>, Q: ParserOf<S>, F: Fn<()>, F::Output: Consumer<Q::Output> {
    type Rest = StarParser<P,Q,F::Output>;
    fn parse(self, value: S) -> GuardedParseResult<Self,S> {
        match self.0.parse(value) {
            Empty(parser) => Empty(PlusParser(parser,self.1)),
            Abort(rest) => Abort(rest),
            Commit(Continue(parsing)) => Commit(Continue(StarParser(self.0,Some(parsing),(self.1)()))),
            Commit(Done(rest,result)) => {
                let mut buffer = (self.1)();
                buffer.push(result);
                Commit(StarParser(self.0,None,buffer).parse(rest))
            }                
        }
    }
}

// ----------- Constant parsers -------------

#[derive(Copy, Clone, Debug)]
pub struct EmitParser<T>(T);

impl<T> Parser for EmitParser<T> {}
impl<T,S> ParserOf<S> for EmitParser<T> {
    type Output = T;
    fn parse(self, value: S) -> ParseResult<Self,S> {
        Done(value,self.0)
    }
    fn done(self) -> T {
        self.0
    }
}

pub fn emit<T>(value: T) -> EmitParser<T> {
    EmitParser(value)
}

#[derive(Debug)]
pub struct CharGuard<F>(F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<F> Copy for CharGuard<F> where F: Copy {}
impl<F> Clone for CharGuard<F> where F: Copy {
    fn clone(&self) -> Self {
        CharGuard(self.0)
    }
}

impl<F> GuardedParser for CharGuard<F> where F: Fn(char) -> bool {}
impl<'a,F> GuardedParserOf<&'a str> for CharGuard<F> where F: Fn(char) -> bool {
    type Rest = EmitParser<char>;
    fn parse(self, value: &'a str) -> GuardedParseResult<Self,&'a str> {
        match value.chars().next() {
            None => Empty(self),
            Some(ch) if (self.0)(ch) => {
                let len = ch.len_utf8();
                Commit(Done(&value[len..],ch))
            },
            Some(_) => Abort(value),
        }
    }
}

pub fn character<F>(f: F) -> CharGuard<F> where F: Fn(char) -> bool {
    CharGuard(f)
}

// ----------- Buffering -------------

// If m is a ParserOf<&'a str>, then
// m.buffer() is a Parser<&'a str> with Output Str<'a>.
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

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Str<'a> {
    Borrowed(&'a str),
    Owned(String),
}

#[derive(Copy, Clone, Debug)]
pub struct BufferedGuardedParser<P>(P);

impl<P> GuardedParser for BufferedGuardedParser<P> where P: GuardedParser {}
impl<'a,P> GuardedParserOf<&'a str> for BufferedGuardedParser<P> where P: GuardedParserOf<&'a str> {
    type Rest = BufferedParser<P::Rest>;
    fn parse(self, value: &'a str) -> GuardedParseResult<Self,&'a str> {
        match self.0.parse(value) {
            Empty(parser) => Empty(BufferedGuardedParser(parser)),
            Commit(Done(rest,_)) => Commit(Done(rest,Borrowed(value.drop_suffix(rest)))),
            Commit(Continue(parsing)) => Commit(Continue(BufferedParser(parsing,String::from(value)))),
            Abort(value) => Abort(value),
        }
    }
}

#[derive(Clone,Debug)]
pub struct BufferedParser<P>(P,String);

impl<P> Parser for BufferedParser<P> where P: Parser {}
impl<'a,P> ParserOf<&'a str> for BufferedParser<P> where P: ParserOf<&'a str> {
    type Output = Str<'a>;
    fn parse(mut self, value: &'a str) -> ParseResult<Self,&'a str> {
        match self.0.parse(value) {
            Done(rest,_) => { self.1.push_str(value.drop_suffix(rest)); Done(rest,Owned(self.1)) },
            Continue(parsing) => { self.1.push_str(value); Continue(BufferedParser(parsing,self.1)) },
        }
    }
    fn done(self) -> Self::Output {
        Owned(self.1)
    }
}

// // ----------- Laziness -------------

// // TODO

// ----------- Tests -------------

#[allow(non_snake_case,dead_code)]
impl<P,S> GuardedParseResult<P,S> where P: GuardedParserOf<S>, P::Rest: ParserOf<S> {

    fn unEmpty(self) -> P {
        match self {
            Empty(p) => p,
            _        => panic!("GuardedParseResult is not empty"),
        }
    }

    fn unAbort(self) -> S {
        match self {
            Abort(s) => s,
            _        => panic!("GuardedParseResult is not failure"),
        }
    }

    fn unCommit(self) -> ParseResult<P::Rest,S> {
        match self {
            Commit(s) => s,
            _       => panic!("GuardedParseResult is not success"),
        }
    }

}

#[allow(non_snake_case,dead_code)]
impl<P,S> ParseResult<P,S> where P: ParserOf<S> {

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
    parser.parse("").unEmpty();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("abc").unCommit().unDone(),("bc",'a'));
}

#[test]
fn test_or_emit() {
    fn mk_x() -> char { 'X' }
    let parser = character(char::is_alphabetic).or_emit(mk_x);
    parser.parse("").unContinue();
    assert_eq!(parser.parse("989").unDone(),("989",'X'));
    assert_eq!(parser.parse("abc").unDone(),("bc",'a'));
}

#[test]
fn test_map() {
    fn mk_none<T>() -> Option<T> { None }
    let parser = character(char::is_alphabetic).map(Some).or_emit(mk_none);
    parser.parse("").unContinue();
    assert_eq!(parser.parse("989").unDone(),("989",None));
    assert_eq!(parser.parse("abc").unDone(),("bc",Some('a')));
}

#[test]
#[allow(non_snake_case)]
fn test_and_then() {
    fn mk_none<T>() -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_emit(mk_none);
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).map(Some).or_emit(mk_none);
    parser.parse("").unContinue();
    assert_eq!(parser.parse("989").unDone(),("989",None));
    assert_eq!(parser.parse("a!").unDone(),("!",Some(('a',None))));
    assert_eq!(parser.parse("abc").unDone(),("c",Some(('a',Some('b')))));
}

#[test]
#[allow(non_snake_case)]
fn test_or_else() {
    fn mk_none<T>() -> Option<T> { None }
    let NUMERIC = character(char::is_numeric).map(Some).or_emit(mk_none);
    let ALPHABETIC = character(char::is_alphabetic).map(Some).or_emit(mk_none);
    let parser = character(char::is_alphabetic).and_then(ALPHABETIC).map(Some).
        or_else(character(char::is_numeric).and_then(NUMERIC).map(Some)).
        or_emit(mk_none);
    parser.parse("").unContinue();
    parser.parse("a").unContinue();
    parser.parse("9").unContinue();
    assert_eq!(parser.parse("!").unDone(),("!",None));
    assert_eq!(parser.parse("a9").unDone(),("9",Some(('a',None))));
    assert_eq!(parser.parse("9a").unDone(),("a",Some(('9',None))));
    assert_eq!(parser.parse("abc").unDone(),("c",Some(('a',Some('b')))));
    assert_eq!(parser.parse("123").unDone(),("3",Some(('1',Some('2')))));
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
    let parser = character(char::is_alphanumeric).star(String::new());
    parser.clone().parse("").unContinue();
    assert_eq!(parser.clone().parse("!!!").unDone(),("!!!",String::from("")));
    assert_eq!(parser.clone().parse("a!").unDone(),("!",String::from("a")));
    assert_eq!(parser.clone().parse("abc98def!").unDone(),("!",String::from("abc98def")));
}

#[test]
#[allow(non_snake_case)]
fn test_buffer() {
    fn mk_none<T>() -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_emit(mk_none );
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).buffer();
    assert_eq!(parser.parse("989").unAbort(),"989");
    assert_eq!(parser.parse("a!").unCommit().unDone(),("!",Borrowed("a")));
    assert_eq!(parser.parse("abc").unCommit().unDone(),("c",Borrowed("ab")));
    let parsing = parser.parse("a").unCommit().unContinue();
    assert_eq!(parsing.parse("bc").unDone(),("c",Owned(String::from("ab"))));
}

#[test]
#[allow(non_snake_case)]
fn test_different_lifetimes() {
    fn go<'a,'b,P>(ab: &'a str, cd: &'b str, parser: P) where P: Clone+for<'c> ParserOf<&'c str,Output=Option<(char,Option<char>)>> {
        let _: &'a str = parser.clone().parse(ab).unDone().0;
        let _: &'b str = parser.clone().parse(cd).unDone().0;
        assert_eq!(parser.clone().parse(ab).unDone(),("",Some(('a',Some('b')))));
        assert_eq!(parser.clone().parse(cd).unDone(),("",Some(('c',Some('d')))));
    }
    fn mk_none<T>() -> Option<T> { None }
    let ALPHANUMERIC = character(char::is_alphanumeric).map(Some).or_emit(mk_none);
    let parser = character(char::is_alphabetic).and_then(ALPHANUMERIC).map(Some).or_emit(mk_none);
    go("ab","cd",parser);
}

