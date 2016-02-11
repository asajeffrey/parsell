//! Provide implementations of parser traits.

use super::{Stateful, Parser, Uncommitted, Committed, Boxable, ParseResult, MaybeParseResult,
            Factory, Function, Consumer, ToPersistent};
use super::ParseResult::{Continue, Done};
use super::MaybeParseResult::{Abort, Commit, Empty};

use self::AndThenStatefulParser::{InLhs, InRhs};
use self::OrElseStatefulParser::{Lhs, Rhs};
use self::OrElseCommittedParser::{Uncommit, CommitLhs, CommitRhs};
use self::OrEmitStatefulParser::{Unresolved, Resolved};

use std::borrow::Cow;
use std::borrow::Cow::{Borrowed, Owned};
use std::iter::Peekable;
use std::fmt::{Formatter, Debug};
use std;

// ----------- N-argument functions ---------------

#[derive(Copy, Clone, Debug)]
pub struct Function2<F>(F);

impl<F> Function2<F> {
    pub fn new(f: F) -> Self {
        Function2(f)
    }
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<F, S1, S2> Function<(S1, S2)> for Function2<F> where F: Fn<(S1, S2, )>
{
    type Output = F::Output;
    fn apply(&self, args: (S1, S2)) -> F::Output {
        (self.0)(args.0, args.1)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Function3<F>(F);

impl<F> Function3<F> {
    pub fn new(f: F) -> Self {
        Function3(f)
    }
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<F, S1, S2, S3> Function<((S1, S2), S3)> for Function3<F> where F: Fn<(S1, S2, S3, )>
{
    type Output = F::Output;
    fn apply(&self, args: ((S1, S2), S3)) -> F::Output {
        (self.0)((args.0).0, (args.0).1, args.1)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Function4<F>(F);

impl<F> Function4<F> {
    pub fn new(f: F) -> Self {
        Function4(f)
    }
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<F, S1, S2, S3, S4> Function<(((S1, S2), S3), S4)> for Function4<F>
    where F: Fn<(S1, S2, S3, S4, )>
{
    type Output = F::Output;
    fn apply(&self, args: (((S1, S2), S3), S4)) -> F::Output {
        (self.0)(((args.0).0).0, ((args.0).0).1, (args.0).1, args.1)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Function5<F>(F);

impl<F> Function5<F> {
    pub fn new(f: F) -> Self {
        Function5(f)
    }
}

// NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// See https://github.com/rust-lang/rust/issues/30867 for more details.
impl<F, S1, S2, S3, S4, S5> Function<((((S1, S2), S3), S4), S5)> for Function5<F>
    where F: Fn<(S1, S2, S3, S4, S5, )>
{
    type Output = F::Output;
    fn apply(&self, args: ((((S1, S2), S3), S4), S5)) -> F::Output {
        (self.0)((((args.0).0).0).0,
                 (((args.0).0).0).1,
                 ((args.0).0).1,
                 (args.0).1,
                 args.1)
    }
}

// ----------- Deal with errors ---------------

#[derive(Copy, Clone, Debug)]
pub struct Try<F>(F);
impl<F, S, E> Function<Result<S, E>> for Try<F> where F: Function<S>
{
    type Output = Result<F::Output,E>;
    fn apply(&self, args: Result<S, E>) -> Result<F::Output, E> {
        Ok(self.0.apply(try!(args)))
    }
}
impl<F> Try<F> {
    pub fn new(f: F) -> Try<F> {
        Try(f)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TryZip;
impl<S, T, E> Function<(Result<S, E>, T)> for TryZip {
    type Output = Result<(S,T),E>;
    fn apply(&self, args: (Result<S, E>, T)) -> Result<(S, T), E> {
        Ok((try!(args.0), args.1))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ZipTry;
impl<S, T, E> Function<(S, Result<T, E>)> for ZipTry {
    type Output = Result<(S,T),E>;
    fn apply(&self, args: (S, Result<T, E>)) -> Result<(S, T), E> {
        Ok((args.0, try!(args.1)))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TryZipTry;
impl<S, T, E> Function<(Result<S, E>, Result<T, E>)> for TryZipTry {
    type Output = Result<(S,T),E>;
    fn apply(&self, args: (Result<S, E>, Result<T, E>)) -> Result<(S, T), E> {
        Ok((try!(args.0), try!(args.1)))
    }
}

// ----------- Map ---------------

#[derive(Debug)]
pub struct MapStatefulParser<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for MapStatefulParser<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for MapStatefulParser<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        MapStatefulParser(self.0.clone(), self.1)
    }
}

impl<P, F, S, T> Stateful<S> for MapStatefulParser<P, F>
    where P: Stateful<S, Output = T>,
          F: Function<T>
{
    type Output = F::Output;
    fn parse(self, value: S) -> ParseResult<Self, S> {
        match self.0.parse(value) {
            Done(rest, result) => Done(rest, self.1.apply(result)),
            Continue(rest, parsing) => Continue(rest, MapStatefulParser(parsing, self.1)),
        }
    }
    fn done(self) -> Self::Output {
        self.1.apply(self.0.done())
    }
}

pub struct MapParser<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for MapParser<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for MapParser<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        MapParser(self.0.clone(), self.1)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<P, F> Debug for MapParser<P, F>
    where P: Debug
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "MapParser({:?}, ...)", self.0)
    }
}

impl<P, F> Parser for MapParser<P, F> {}
impl<P, F, S> Uncommitted<S> for MapParser<P, F>
    where P: Uncommitted<S>,
          F: Copy + Function<P::Output>
{
    type Output = F::Output;
    type State = MapStatefulParser<P::State,F>;
    fn parse(&self, value: S) -> MaybeParseResult<Self::State, S> {
        match self.0.parse(value) {
            Empty(rest) => Empty(rest),
            Commit(Done(rest, result)) => Commit(Done(rest, self.1.apply(result))),
            Commit(Continue(rest, parsing)) => {
                Commit(Continue(rest, MapStatefulParser(parsing, self.1)))
            }
            Abort(value) => Abort(value),
        }
    }
}
impl<P, F, S> Committed<S> for MapParser<P, F>
    where P: Committed<S>,
          F: Copy + Function<P::Output>
{
    type Output = F::Output;
    type State = MapStatefulParser<P::State,F>;
    fn init(&self) -> Self::State {
        MapStatefulParser(self.0.init(), self.1)
    }
}

impl<P, F> MapParser<P, F> {
    pub fn new(parser: P, function: F) -> Self {
        MapParser(parser, function)
    }
}

// ----------- Sequencing ---------------

#[derive(Copy, Clone, Debug)]
pub struct AndThenParser<P, Q>(P, Q);

impl<P, Q> Parser for AndThenParser<P, Q> {}
impl<P, Q, S> Committed<S> for AndThenParser<P, Q>
    where P: Committed<S>,
          Q: Committed<S>,
          P::Output: ToPersistent,
{
    type Output = (P::Output,Q::Output);
    type State = AndThenStatefulParser<P::State,Q::State,<P::Output as ToPersistent>::Persistent>;
    fn init(&self) -> Self::State {
        InLhs(self.0.init(), self.1.init())
    }
}
impl<P, Q, S> Uncommitted<S> for AndThenParser<P, Q>
    where P: Uncommitted<S>,
          Q: Committed<S>,
          P::Output: ToPersistent,
{
    type Output = (P::Output,Q::Output);
    type State = AndThenStatefulParser<P::State,Q::State,<P::Output as ToPersistent>::Persistent>;
    fn parse(&self, value: S) -> MaybeParseResult<Self::State, S> {
        match self.0.parse(value) {
            Empty(rest) => Empty(rest),
            Commit(Done(rest, result1)) => {
                match self.1.init().parse(rest) {
                    Done(rest, result2) => Commit(Done(rest, (result1, result2))),
                    Continue(rest, parsing) => Commit(Continue(rest, InRhs(result1.to_persistent(), parsing))),
                }
            }
            Commit(Continue(rest, parsing)) => {
                Commit(Continue(rest, InLhs(parsing, self.1.init())))
            }
            Abort(value) => Abort(value),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum AndThenStatefulParser<P, Q, T> {
    InLhs(P, Q),
    InRhs(T, Q),
}

impl<P, Q, S> Stateful<S> for AndThenStatefulParser<P, Q, <P::Output as ToPersistent>::Persistent>
    where P: Stateful<S>,
          Q: Stateful<S>,
          P::Output: ToPersistent,
{
    type Output = (P::Output,Q::Output);
    fn parse(self, value: S) -> ParseResult<Self, S> {
        match self {
            InLhs(lhs, rhs) => {
                match lhs.parse(value) {
                    Done(rest, result1) => {
                        match rhs.parse(rest) {
                            Done(rest, result2) => Done(rest, (result1, result2)),
                            Continue(rest, parsing) => Continue(rest, InRhs(result1.to_persistent(), parsing)),
                        }
                    }
                    Continue(rest, parsing) => Continue(rest, InLhs(parsing, rhs)),
                }
            }
            InRhs(result1, rhs) => {
                match rhs.parse(value) {
                    Done(rest, result2) => Done(rest, (ToPersistent::from_persistent(result1), result2)),
                    Continue(rest, parsing) => Continue(rest, InRhs(result1, parsing)),
                }
            }
        }
    }
    fn done(self) -> Self::Output {
        match self {
            InLhs(lhs, rhs) => (lhs.done(), rhs.done()),
            InRhs(result1, rhs) => (ToPersistent::from_persistent(result1), rhs.done()),
        }
    }
}

impl<P, Q> AndThenParser<P, Q> {
    pub fn new(lhs: P, rhs: Q) -> Self {
        AndThenParser(lhs, rhs)
    }
}

// ----------- Choice ---------------

#[derive(Copy, Clone, Debug)]
pub struct OrElseParser<P, Q>(P, Q);

impl<P, Q> Parser for OrElseParser<P, Q> {}
impl<P, Q, S> Committed<S> for OrElseParser<P, Q>
    where P: Copy + Uncommitted<S>,
          Q: Committed<S, Output = P::Output>
{
    type Output = P::Output;
    type State = OrElseCommittedParser<P,P::State,Q::State>;
    fn init(&self) -> Self::State {
        Uncommit(self.0, self.1.init())
    }
}
impl<P, Q, S> Uncommitted<S> for OrElseParser<P, Q>
    where P: Uncommitted<S>,
          Q: Uncommitted<S, Output = P::Output>
{
    type Output = P::Output;
    type State = OrElseStatefulParser<P::State,Q::State>;
    fn parse(&self, value: S) -> MaybeParseResult<Self::State, S> {
        match self.0.parse(value) {
            Empty(rest) => Empty(rest),
            Commit(Done(rest, result)) => Commit(Done(rest, result)),
            Commit(Continue(rest, parsing)) => Commit(Continue(rest, Lhs(parsing))),
            Abort(value) => {
                match self.1.parse(value) {
                    Empty(rest) => Empty(rest),
                    Commit(Done(rest, result)) => Commit(Done(rest, result)),
                    Commit(Continue(rest, parsing)) => Commit(Continue(rest, Rhs(parsing))),
                    Abort(value) => Abort(value),
                }
            }
        }
    }
}

impl<P, Q> OrElseParser<P, Q> {
    pub fn new(lhs: P, rhs: Q) -> Self {
        OrElseParser(lhs, rhs)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum OrElseStatefulParser<P, Q> {
    Lhs(P),
    Rhs(Q),
}

impl<P, Q, S> Stateful<S> for OrElseStatefulParser<P, Q>
    where P: Stateful<S>,
          Q: Stateful<S, Output = P::Output>
{
    type Output = P::Output;
    fn parse(self, value: S) -> ParseResult<Self, S> {
        match self {
            Lhs(lhs) => {
                match lhs.parse(value) {
                    Done(rest, result) => Done(rest, result),
                    Continue(rest, parsing) => Continue(rest, Lhs(parsing)),
                }
            }
            Rhs(rhs) => {
                match rhs.parse(value) {
                    Done(rest, result) => Done(rest, result),
                    Continue(rest, parsing) => Continue(rest, Rhs(parsing)),
                }
            }
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
pub enum OrElseCommittedParser<P, Q, R> {
    Uncommit(P, R),
    CommitLhs(Q),
    CommitRhs(R),
}

impl<P, Q, S> Stateful<S> for OrElseCommittedParser<P, P::State, Q>
    where P: Uncommitted<S>,
          Q: Stateful<S, Output = P::Output>
{
    type Output = P::Output;
    fn parse(self, value: S) -> ParseResult<Self, S> {
        match self {
            Uncommit(lhs, rhs) => {
                match lhs.parse(value) {
                    Empty(value) => Continue(value, Uncommit(lhs, rhs)),
                    Commit(Done(rest, result)) => Done(rest, result),
                    Commit(Continue(rest, parsing)) => Continue(rest, CommitLhs(parsing)),
                    Abort(value) => {
                        match rhs.parse(value) {
                            Done(rest, result) => Done(rest, result),
                            Continue(rest, parsing) => Continue(rest, CommitRhs(parsing)),
                        }
                    }
                }
            }
            CommitLhs(lhs) => {
                match lhs.parse(value) {
                    Done(rest, result) => Done(rest, result),
                    Continue(rest, parsing) => Continue(rest, CommitLhs(parsing)),
                }
            }
            CommitRhs(rhs) => {
                match rhs.parse(value) {
                    Done(rest, result) => Done(rest, result),
                    Continue(rest, parsing) => Continue(rest, CommitRhs(parsing)),
                }
            }
        }
    }
    fn done(self) -> Self::Output {
        match self {
            Uncommit(_, rhs) => rhs.done(),
            CommitLhs(lhs) => lhs.done(),
            CommitRhs(rhs) => rhs.done(),
        }
    }
}

#[derive(Debug)]
pub enum OrEmitStatefulParser<P, F, R> {
    Unresolved(P, F),
    Resolved(R),
}

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F, R> Copy for OrEmitStatefulParser<P, F, R>
    where P: Copy,
          F: Copy,
          R: Copy
{}
impl<P, F, R> Clone for OrEmitStatefulParser<P, F, R>
    where P: Copy,
          F: Copy,
          R: Clone
{
    fn clone(&self) -> Self {
        match *self {
            Unresolved(parser, default) => Unresolved(parser, default),
            Resolved(ref parser) => Resolved(parser.clone()),
        }
    }
}

impl<P, F, S> Stateful<S> for OrEmitStatefulParser<P, F, P::State>
    where P: Uncommitted<S>,
          F: Factory<Output = P::Output>
{
    type Output = P::Output;
    fn parse(self, value: S) -> ParseResult<Self, S> {
        match self {
            Unresolved(parser, default) => {
                match parser.parse(value) {
                    Empty(rest) => Continue(rest, Unresolved(parser, default)),
                    Commit(Done(rest, result)) => Done(rest, result),
                    Commit(Continue(rest, parsing)) => Continue(rest, Resolved(parsing)),
                    Abort(value) => Done(value, default.build()),
                }
            }
            Resolved(parser) => {
                match parser.parse(value) {
                    Done(rest, result) => Done(rest, result),
                    Continue(rest, parsing) => Continue(rest, Resolved(parsing)),
                }
            }
        }
    }
    fn done(self) -> Self::Output {
        match self {
            Unresolved(_, default) => default.build(),
            Resolved(parser) => parser.done(),
        }
    }
}

pub struct OrEmitParser<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for OrEmitParser<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for OrEmitParser<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        OrEmitParser(self.0.clone(), self.1)
    }
}

impl<P, F> Parser for OrEmitParser<P, F> {}
impl<P, F, S> Committed<S> for OrEmitParser<P, F>
    where P: Clone + Uncommitted<S>,
          F: Copy + Factory<Output = P::Output>
{
    type Output = P::Output;
    type State = OrEmitStatefulParser<P,F,P::State>;
    fn init(&self) -> Self::State {
        Unresolved(self.0.clone(), self.1)
    }
}

impl<P, F> OrEmitParser<P, F> {
    pub fn new(parser: P, default: F) -> Self {
        OrEmitParser(parser, default)
    }
}

// ----------- Kleene star ---------------

#[derive(Clone,Debug)]
pub struct StarStatefulParser<P, Q, T>(P, Option<Q>, T);

impl<P, T, S> Stateful<S> for StarStatefulParser<P, P::State, T>
    where P: Copy + Uncommitted<S>,
          T: Consumer<P::Output>
{
    type Output = T;
    fn parse(mut self, mut value: S) -> ParseResult<Self, S> {
        loop {
            match self.1.take() {
                None => {
                    match self.0.parse(value) {
                        Empty(rest) => {
                            return Continue(rest, StarStatefulParser(self.0, None, self.2))
                        }
                        Commit(Continue(rest, parsing)) => {
                            return Continue(rest,
                                            StarStatefulParser(self.0, Some(parsing), self.2))
                        }
                        Commit(Done(rest, result)) => {
                            self.2.accept(result);
                            value = rest;
                        }
                        Abort(rest) => return Done(rest, self.2),
                    }
                }
                Some(parser) => {
                    match parser.parse(value) {
                        Continue(rest, parsing) => {
                            return Continue(rest,
                                            StarStatefulParser(self.0, Some(parsing), self.2))
                        }
                        Done(rest, result) => {
                            self.2.accept(result);
                            value = rest;
                        }
                    }
                }
            }
        }
    }
    fn done(self) -> T {
        self.2
    }
}

pub struct PlusParser<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for PlusParser<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for PlusParser<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        PlusParser(self.0.clone(), self.1)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<P, F> Debug for PlusParser<P, F>
    where P: Debug
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "PlusParser({:?}, ...)", self.0)
    }
}

impl<P, F> Parser for PlusParser<P, F> {}
impl<P, F, S> Uncommitted<S> for PlusParser<P, F>
    where P: Copy + Uncommitted<S>,
          F: Factory,
          F::Output: Consumer<P::Output>
{
    type Output = F::Output;
    type State = StarStatefulParser<P,P::State,F::Output>;
    fn parse(&self, value: S) -> MaybeParseResult<Self::State, S> {
        match self.0.parse(value) {
            Empty(rest) => Empty(rest),
            Abort(rest) => Abort(rest),
            Commit(Continue(rest, parsing)) => {
                Commit(Continue(rest,
                                StarStatefulParser(self.0, Some(parsing), self.1.build())))
            }
            Commit(Done(rest, result)) => {
                let mut buffer = self.1.build();
                buffer.accept(result);
                Commit(StarStatefulParser(self.0, None, buffer).parse(rest))
            }
        }
    }
}

impl<P, F> PlusParser<P, F> {
    pub fn new(parser: P, factory: F) -> Self {
        PlusParser(parser, factory)
    }
}

pub struct StarParser<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for StarParser<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for StarParser<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        StarParser(self.0.clone(), self.1)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<P, F> Debug for StarParser<P, F>
    where P: Debug
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "StarParser({:?}, ...)", self.0)
    }
}

impl<P, F> Parser for StarParser<P, F> {}
impl<P, F, S> Committed<S> for StarParser<P, F>
    where P: Copy + Uncommitted<S>,
          F: Factory,
          F::Output: Consumer<P::Output>
{
    type Output = F::Output;
    type State = StarStatefulParser<P,P::State,F::Output>;
    fn init(&self) -> Self::State {
        StarStatefulParser(self.0, None, self.1.build())
    }
}

impl<P, F> StarParser<P, F> {
    pub fn new(parser: P, factory: F) -> Self {
        StarParser(parser, factory)
    }
}

// ----------- A type for empty parsers -------------

#[derive(Copy, Clone, Debug)]
enum Impossible {}

impl Impossible {
    fn cant_happen<T>(&self) -> T {
        match *self {}
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ImpossibleStatefulParser<T>(Impossible, T);

impl<T, S> Stateful<S> for ImpossibleStatefulParser<T> {
    type Output = T;
    fn parse(self, _: S) -> ParseResult<Self, S> {
        self.0.cant_happen()
    }
    fn done(self) -> T {
        self.0.cant_happen()
    }
}

// ----------- Character parsers -------------

pub struct CharacterParser<F>(F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<F> Copy for CharacterParser<F> where F: Copy
{}
impl<F> Clone for CharacterParser<F> where F: Copy
{
    fn clone(&self) -> Self {
        CharacterParser(self.0)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<F> Debug for CharacterParser<F>
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "CharacterParser(...)")
    }
}

impl<F> Parser for CharacterParser<F> {}
impl<'a, F> Uncommitted<&'a str> for CharacterParser<F> where F: Function<char, Output = bool>
{
    type Output = char;
    type State = ImpossibleStatefulParser<char>;
    fn parse(&self, value: &'a str) -> MaybeParseResult<Self::State, &'a str> {
        match value.chars().next() {
            None => Empty(value),
            Some(ch) if self.0.apply(ch) => {
                let len = ch.len_utf8();
                Commit(Done(&value[len..], ch))
            }
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
    fn parse(self, value: &'a str) -> ParseResult<Self, &'a str> {
        match value.chars().next() {
            None => Continue(value, AnyCharacterParser),
            Some(ch) => {
                let len = ch.len_utf8();
                Done(&value[len..], Some(ch))
            }
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

pub struct TokenParser<F>(F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<F> Copy for TokenParser<F> where F: Copy
{}
impl<F> Clone for TokenParser<F> where F: Copy
{
    fn clone(&self) -> Self {
        TokenParser(self.0)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<F> Debug for TokenParser<F>
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "TokenParser(...)")
    }
}

impl<F> Parser for TokenParser<F> {}
impl<F, I> Uncommitted<Peekable<I>> for TokenParser<F>
    where F: for<'a> Function<&'a I::Item, Output = bool>,
          I: Iterator
{
    type Output = I::Item;
    type State = ImpossibleStatefulParser<I::Item>;
    fn parse(&self, mut iterator: Peekable<I>) -> MaybeParseResult<Self::State, Peekable<I>> {
        let matched = match iterator.peek() {
            None => None,
            Some(tok) => Some(self.0.apply(tok)),
        };
        match matched {
            None => Empty(iterator),
            Some(true) => {
                let tok = iterator.next().unwrap();
                Commit(Done(iterator, tok))
            }
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
impl<I> Stateful<I> for AnyTokenParser where I: Iterator
{
    type Output = Option<I::Item>;
    fn parse(self, mut iter: I) -> ParseResult<Self, I> {
        match iter.next() {
            None => Continue(iter, AnyTokenParser),
            Some(tok) => Done(iter, Some(tok)),
        }
    }
    fn done(self) -> Self::Output {
        None
    }
}
impl<I> Committed<I> for AnyTokenParser where I: Iterator
{
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
impl<'a, P> Uncommitted<&'a str> for BufferedParser<P> where P: Uncommitted<&'a str>
{
    type Output = Cow<'a,str>;
    type State = BufferedStatefulParser<P::State>;
    fn parse(&self, value: &'a str) -> MaybeParseResult<Self::State, &'a str> {
        match self.0.parse(value) {
            Empty(rest) => Empty(rest),
            Commit(Done(rest, _)) => {
                Commit(Done(rest, Borrowed(&value[..(value.len() - rest.len())])))
            }
            Commit(Continue(rest, parsing)) => {
                Commit(Continue(rest, BufferedStatefulParser(parsing, String::from(value))))
            }
            Abort(value) => Abort(value),
        }
    }
}
impl<'a, P> Committed<&'a str> for BufferedParser<P> where P: Committed<&'a str>
{
    type Output = Cow<'a,str>;
    type State = BufferedStatefulParser<P::State>;
    fn init(&self) -> Self::State {
        BufferedStatefulParser(self.0.init(), String::new())
    }
}

impl<P> BufferedParser<P> {
    pub fn new(parser: P) -> Self {
        BufferedParser(parser)
    }
}

#[derive(Clone,Debug)]
pub struct BufferedStatefulParser<P>(P, String);

impl<'a, P> Stateful<&'a str> for BufferedStatefulParser<P> where P: Stateful<&'a str>
{
    type Output = Cow<'a,str>;
    fn parse(mut self, value: &'a str) -> ParseResult<Self, &'a str> {
        match self.0.parse(value) {
            Done(rest, _) if self.1.is_empty() => {
                Done(rest, Borrowed(&value[..(value.len() - rest.len())]))
            }
            Done(rest, _) => {
                self.1.push_str(&value[..(value.len() - rest.len())]);
                Done(rest, Owned(self.1))
            }
            Continue(rest, parsing) => {
                self.1.push_str(value);
                Continue(rest, BufferedStatefulParser(parsing, self.1))
            }
        }
    }
    fn done(self) -> Self::Output {
        Owned(self.1)
    }
}

// ----------- Parsers which are boxable -------------

#[derive(Debug)]
pub struct BoxableParser<P>(Option<P>);
impl<P, S> Boxable<S> for BoxableParser<P> where P: Stateful<S>
{
    type Output = P::Output;
    fn parse_boxable(&mut self, value: S) -> (S, Option<Self::Output>) {
        match self.0.take().unwrap().parse(value) {
            Done(rest, result) => (rest, Some(result)),
            Continue(rest, parsing) => {
                self.0 = Some(parsing);
                (rest, None)
            }
        }
    }
    fn done_boxable(&mut self) -> Self::Output {
        self.0.take().unwrap().done()
    }
}

impl<P: ?Sized, S> Stateful<S> for Box<P> where P: Boxable<S>
{
    type Output = P::Output;
    fn parse(mut self, value: S) -> ParseResult<Self, S> {
        match self.parse_boxable(value) {
            (rest, Some(result)) => Done(rest, result),
            (rest, None) => Continue(rest, self),
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

// ----------- Iterate over parse results -------------

#[derive(Copy, Clone, Debug)]
pub struct IterParser<P, Q, S>(P, Option<(Q, S)>);

impl<P, S> Iterator for IterParser<P, P::State, S> where P: Copy + Committed<S>
{
    type Item = P::Output;
    fn next(&mut self) -> Option<P::Output> {
        let (state, result) = match self.1.take() {
            None => (None, None),
            Some((parsing, data)) => {
                match parsing.parse(data) {
                    Done(rest, result) => (Some((self.0.init(), rest)), Some(result)),
                    Continue(rest, parsing) => (Some((parsing, rest)), None),
                }
            }
        };
        *self = IterParser(self.0, state);
        result
    }
}

impl<P, S> IterParser<P, P::State, S> where P: Copy + Committed<S>
{
    pub fn new(parser: P, data: S) -> Self {
        IterParser(parser, Some((parser.init(), data)))
    }
}

// ----------- Pipe parsers -------------

#[derive(Copy, Clone, Debug)]
pub struct PipeStateful<P, Q, R>(P, Q, R);

impl<P, Q, S, T> Stateful<S> for PipeStateful<P, P::State, Q>
    where P: Copy + Committed<S>,
          Q: for<'a> Stateful<Peekable<&'a mut IterParser<P, P::State, S>>, Output = T>
{
    type Output = T;
    fn parse(self, data: S) -> ParseResult<Self, S> {
        let mut iter = IterParser(self.0, Some((self.1, data)));
        match self.2.parse(iter.by_ref().peekable()) {
            Done(_, result) => Done(iter.1.unwrap().1, result),
            Continue(_, parsing2) => {
                let (parsing1, data) = iter.1.unwrap();
                Continue(data, PipeStateful(self.0, parsing1, parsing2))
            }
        }
    }
    fn done(self) -> T {
        // TODO: feed the output of self.1.done() into self.2.
        self.1.done();
        self.2.done()
    }
}

#[derive(Copy, Clone, Debug)]
pub struct PipeParser<P, Q>(P, Q);

impl<P, Q> Parser for PipeParser<P, Q> {}
impl<P, Q, R, S, T> Committed<S> for PipeParser<P, Q>
    where P: Copy + Committed<S>,
          Q: for<'a> Committed<Peekable<&'a mut IterParser<P, P::State, S>>,
                               State = R,
                               Output = T>,
          R: for<'a> Stateful<Peekable<&'a mut IterParser<P, P::State, S>>, Output = T>
{
    type State = PipeStateful<P,P::State,R>;
    type Output = T;
    fn init(&self) -> Self::State {
        PipeStateful(self.0, self.0.init(), self.1.init())
    }
}

impl<P, Q> PipeParser<P, Q> {
    pub fn new(lhs: P, rhs: Q) -> Self {
        PipeParser(lhs, rhs)
    }
}

