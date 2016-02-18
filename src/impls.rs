//! Provide implementations of parser traits.

use super::{Parser, ParseResult};
use super::{Stateful, Committed, Uncommitted, Boxable};
use super::{Function, Consumer, Factory, PeekableIterator};
use super::{Upcast, ToStatic};
use super::ParseResult::{Done, Continue, Backtrack};

use self::OrElseState::{Lhs, Rhs};
use self::AndThenState::{InLhs, InBetween, InRhs};

use std::borrow::Cow;
use std::borrow::Cow::{Borrowed, Owned};
use std::str::Chars;
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

// ----------- Deal with options ---------------

#[derive(Copy, Clone, Debug)]
pub struct MkSome;
impl<T> Function<T> for MkSome
{
    type Output = Option<T>;
    fn apply(&self, arg: T) -> Option<T> {
        Some(arg)
    }
}

// ----------- Map ---------------

pub struct Map<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for Map<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for Map<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        Map(self.0.clone(), self.1)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<P, F> Debug for Map<P, F>
    where P: Debug
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "Map({:?}, ...)", self.0)
    }
}

impl<P, F> Parser for Map<P, F> {}

impl<P, F, Ch, Str> Stateful<Ch, Str> for Map<P, F>
    where P: Stateful<Ch, Str>,
          F: Function<P::Output>,
          Str: Iterator<Item = Ch>,
{
    
    type Output = F::Output;

    fn done(self) -> F::Output {
        self.1.apply(self.0.done())
    }

    fn more(self, string: &mut Str) -> ParseResult<Self, F::Output> {
        match self.0.more(string) {
            Backtrack => Backtrack,
            Done(result) => Done(self.1.apply(result)),
            Continue(state) => Continue(Map(state, self.1)),
        }
    }

}

impl<P, F, Ch, Str> Committed<Ch, Str> for Map<P, F>
    where P: Committed<Ch, Str>,
          F: 'static + Copy + Function<P::Output>,
          Str: Iterator<Item = Ch>,
{

    type Output = F::Output;
    type State = Map<P::State, F>;
    
    fn init(&self, string: &mut Str) -> ParseResult<Self::State, F::Output> {
        match self.0.init(string) {
            Backtrack => Backtrack,
            Done(result) => Done(self.1.apply(result)),
            Continue(state) => Continue(Map(state, self.1)),
        }
    }

    fn empty(&self) -> F::Output {
        self.1.apply(self.0.empty())
    }
    
}

impl<P, F, Ch, Str> Uncommitted<Ch, Str> for Map<P, F>
    where P: Uncommitted<Ch, Str>,
          F: 'static + Copy + Function<P::Output>,
          Str: Iterator<Item = Ch>,
{

    type Output = F::Output;
    type State = Map<P::State, F>;
    
    fn init_maybe(&self, string: &mut Str) -> ParseResult<Self::State, F::Output> {
        match self.0.init_maybe(string) {
            Backtrack => Backtrack,
            Done(result) => Done(self.1.apply(result)),
            Continue(state) => Continue(Map(state, self.1)),
        }
    }

}

impl<P, F> Map<P, F> {
    pub fn new(p: P, f: F) -> Self {
        Map(p, f)
    }
}

// ----------- Sequencing ---------------

#[derive(Copy, Clone, Debug)]
pub struct AndThen<P, Q>(P, Q);

impl<P, Q> Parser for AndThen<P, Q> {}

impl<P, Q, Ch, Str, PStaticOutput> Committed<Ch, Str> for AndThen<P, Q>
    where P: Committed<Ch, Str>,
          Q: 'static + Copy + Committed<Ch, Str>,
          Str: Iterator<Item = Ch>,
          PStaticOutput: 'static + Upcast<P::Output>,
          P::Output: ToStatic<Static = PStaticOutput>,
{

    type Output = (P::Output, Q::Output);
    type State = AndThenState<P::State, Q, PStaticOutput, Q::State>;

    fn init(&self, string: &mut Str) -> ParseResult<Self::State, Self::Output> {
        match self.0.init(string) {
            Backtrack => Backtrack,
            Done(fst) => match self.1.init(string) {
                Backtrack => Continue(InBetween(fst.to_static(), self.1)),
                Done(snd) => Done((fst, snd)),
                Continue(snd) => Continue(InRhs(fst.to_static(), snd)),
            },
            Continue(fst) => Continue(InLhs(fst, self.1)),
        }
    }

    fn empty(&self) -> Self::Output {
        (self.0.empty(), self.1.empty())
    }
    
}

impl<P, Q, Ch, Str, PStaticOutput> Uncommitted<Ch, Str> for AndThen<P, Q>
    where P: Uncommitted<Ch, Str>,
          Q: 'static + Copy + Committed<Ch, Str>,
          Str: Iterator<Item = Ch>,
          PStaticOutput: 'static + Upcast<P::Output>,
          P::Output: ToStatic<Static = PStaticOutput>,
{

    type Output = (P::Output, Q::Output);
    type State = AndThenState<P::State, Q, PStaticOutput, Q::State>;

    fn init_maybe(&self, string: &mut Str) -> ParseResult<Self::State, Self::Output> {
        match self.0.init_maybe(string) {
            Backtrack => Backtrack,
            Done(fst) => match self.1.init(string) {
                Backtrack => Continue(InBetween(fst.to_static(), self.1)),
                Done(snd) => Done((fst, snd)),
                Continue(snd) => Continue(InRhs(fst.to_static(), snd)),
            },
            Continue(fst) => Continue(InLhs(fst, self.1)),
        }
    }

}

impl<P, Q> AndThen<P, Q> {
    pub fn new(p: P, q: Q) -> Self {
        AndThen(p, q)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum AndThenState<PState, Q, PStaticOutput, QState> {
    InLhs(PState, Q),
    InBetween(PStaticOutput, Q),
    InRhs(PStaticOutput, QState),
}

impl<PState, Q, Ch, Str, PStaticOutput> Stateful<Ch, Str> for AndThenState<PState, Q, PStaticOutput, Q::State>
    where PState: Stateful<Ch, Str>,
          Q: Committed<Ch, Str>,
          Str: Iterator<Item = Ch>,
          PStaticOutput: 'static + Upcast<PState::Output>,
          PState::Output: ToStatic<Static = PStaticOutput>,

{
    
    type Output = (PState::Output, Q::Output);

    fn done(self) -> Self::Output
    {
        match self {
            InLhs(fst, snd) => (fst.done(), snd.empty()),
            InBetween(fst, snd) => (fst.upcast(), snd.empty()),
            InRhs(fst, snd) => (fst.upcast(), snd.done()),
        }
    }

    fn more(self, string: &mut Str) -> ParseResult<Self, Self::Output>
    {
        match self {
            InLhs(fst, snd) => {
                match fst.more(string) {
                    Done(fst) => match snd.init(string) {
                        Backtrack => Continue(InBetween(fst.to_static(), snd)),
                        Done(snd) => Done((fst, snd)),
                        Continue(snd) => Continue(InRhs(fst.to_static(), snd)),
                    },
                    Backtrack => Backtrack,
                    Continue(fst) => Continue(InLhs(fst, snd)),
                }
            }
            InBetween(fst, snd) => {
                match snd.init(string) {
                    Backtrack => Backtrack,
                    Done(snd) => Done((fst.upcast(), snd)),
                    Continue(snd) => Continue(InRhs(fst, snd)),
                }
            }
            InRhs(fst, snd) => {
                match snd.more(string) {
                    Backtrack => Backtrack,
                    Done(snd) => Done((fst.upcast(), snd)),
                    Continue(snd) => Continue(InRhs(fst, snd)),
                }
            }
        }
    }
   
}

// ----------- Choice ---------------

#[derive(Copy, Clone, Debug)]
pub struct OrElse<P, Q>(P, Q);

impl<P, Q> Parser for OrElse<P, Q> {}

impl<P, Q, Ch, Str> Committed<Ch, Str> for OrElse<P, Q>
    where P: Uncommitted<Ch, Str>,
          Q: Committed<Ch, Str, Output = P::Output>,
          Str: Iterator<Item = Ch>,
{
    
    type Output = P::Output;
    type State = OrElseState<P::State, Q::State>;

    fn init(&self, string: &mut Str) -> ParseResult<Self::State, Self::Output> {
        match self.0.init_maybe(string) {
            Done(result) => Done(result),
            Continue(lhs) => Continue(Lhs(lhs)),
            Backtrack => match self.1.init(string) {
                Backtrack => Backtrack,
                Done(result) => Done(result),
                Continue(rhs) => Continue(Rhs(rhs)),
            },
        }
    }

    fn empty(&self) -> P::Output {
        self.1.empty()
    }
    
}

impl<P, Q, Ch, Str> Uncommitted<Ch, Str> for OrElse<P, Q>
    where P: Uncommitted<Ch, Str>,
          Q: Uncommitted<Ch, Str, Output = P::Output>,
          Str: Iterator<Item = Ch>,
{

    type Output = P::Output;
    type State = OrElseState<P::State, Q::State>;

    fn init_maybe(&self, string: &mut Str) -> ParseResult<Self::State, Self::Output> {
        match self.0.init_maybe(string) {
            Done(result) => Done(result),
            Continue(lhs) => Continue(Lhs(lhs)),
            Backtrack => match self.1.init_maybe(string) {
                Done(result) => Done(result),
                Continue(rhs) => Continue(Rhs(rhs)),
                Backtrack => Backtrack,
            },
        }
    }
    
}

impl<P, Q> OrElse<P, Q> {
    pub fn new(lhs: P, rhs: Q) -> Self {
        OrElse(lhs, rhs)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum OrElseState<P, Q> {
    Lhs(P),
    Rhs(Q),
}

impl<P, Q, Ch, Str> Stateful<Ch, Str> for OrElseState<P, Q>
    where P: Stateful<Ch, Str>,
          Q: Stateful<Ch, Str, Output = P::Output>,
          Str: Iterator<Item = Ch>,
{
    type Output = P::Output;
    
    fn more(self, string: &mut Str) -> ParseResult<Self, P::Output> {
        match self {
            Lhs(lhs) => match lhs.more(string) {
                Backtrack => Backtrack,
                Done(result) => Done(result),
                Continue(lhs) => Continue(Lhs(lhs)),
            },
            Rhs(rhs) => match rhs.more(string) {
                Backtrack => Backtrack,
                Done(result) => Done(result),
                Continue(rhs) => Continue(Rhs(rhs)),
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

// ----------- Kleene star ---------------

#[derive(Clone,Debug)]
pub struct StarState<P, PState, T>(P, Option<PState>, T);

impl<P, PState, T, Ch, Str> Stateful<Ch, Str> for StarState<P, PState, T>
    where P: Copy + Uncommitted<Ch, Str, State = PState>,
          PState: 'static + Stateful<Ch, Str, Output = P::Output>,
          T: Consumer<P::Output>,
          Str: PeekableIterator<Item = Ch>,
{
    type Output = T;
    fn more(mut self, string: &mut Str) -> ParseResult<Self, T> {
        loop {
            match self.1.take() {
                None => {
                    match self.0.init_maybe(string) {
                        Continue(state) => return Continue(StarState(self.0, Some(state), self.2)),
                        Done(result) => self.2.accept(result),
                        Backtrack => return if string.is_empty() {
                            Continue(self)
                        } else {
                            Done(self.2)
                        },
                    }
                }
                Some(state) => {
                    match state.more(string) {
                        Backtrack => panic!("stateful parsers shouldn't backtrack"),
                        Continue(state) => return Continue(StarState(self.0, Some(state), self.2)),
                        Done(result) => self.2.accept(result),
                    }
                }
            }
        }
    }
    fn done(self) -> T {
        self.2
    }
}

pub struct Plus<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for Plus<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for Plus<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        Plus(self.0.clone(), self.1)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<P, F> Debug for Plus<P, F>
    where P: Debug
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "Plus({:?}, ...)", self.0)
    }
}

impl<P, F> Parser for Plus<P, F> {}

impl<P, F, Ch, Str> Uncommitted<Ch, Str> for Plus<P, F>
    where P: 'static + Copy + Uncommitted<Ch, Str>,
          F: 'static + Factory,
          Str: PeekableIterator<Item = Ch>,
          P::State: 'static + Stateful<Ch, Str>,
          F::Output: Consumer<<P as Uncommitted<Ch, Str>>::Output>,
{
    type State = StarState<P, P::State, F::Output>;
    type Output = F::Output;
        
    fn init_maybe(&self, string: &mut Str) -> ParseResult<Self::State, F::Output> {
        match self.0.init_maybe(string) {
            Backtrack => Backtrack,
            Continue(state) => Continue(StarState(self.0, Some(state), self.1.build())),
            Done(result) => {
                let mut buffer = self.1.build();
                buffer.accept(result);
                StarState(self.0, None, buffer).more(string)
            },
        }
    }
}

impl<P, F> Plus<P, F> {
    pub fn new(parser: P, factory: F) -> Self {
        Plus(parser, factory)
    }
}

pub struct Star<P, F>(P, F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<P, F> Copy for Star<P, F>
    where P: Copy,
          F: Copy
{}
impl<P, F> Clone for Star<P, F>
    where P: Clone,
          F: Copy
{
    fn clone(&self) -> Self {
        Star(self.0.clone(), self.1)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<P, F> Debug for Star<P, F>
    where P: Debug
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "Star({:?}, ...)", self.0)
    }
}

impl<P, F> Parser for Star<P, F> {}

impl<P, F, Ch, Str> Committed<Ch, Str> for Star<P, F>
    where P: 'static + Copy + Uncommitted<Ch, Str>,
          F: 'static + Factory,
          Str: PeekableIterator<Item = Ch>,
          P::State: 'static + Stateful<Ch, Str>,
          F::Output: Consumer<<P as Uncommitted<Ch, Str>>::Output>,
{
    type State = StarState<P, P::State, F::Output>;
    type Output = F::Output;
        
    fn init(&self, string: &mut Str) -> ParseResult<Self::State, F::Output> {
        StarState(self.0, None, self.1.build()).more(string)
    }

    fn empty(&self) -> F::Output {
        self.1.build()
    }
    
}

impl<P, F> Star<P, F> {
    pub fn new(parser: P, factory: F) -> Self {
        Star(parser, factory)
    }
}

// ----------- A type for parsers which immediately emit a result -------------

#[derive(Copy, Clone, Debug)]
pub struct Emit<F>(F);

impl<F> Parser for Emit<F> {}

impl<F, Ch, Str> Stateful<Ch, Str> for Emit<F>
    where Str: Iterator<Item = Ch>,
          F: Factory,
{

    type Output = F::Output;

    fn more(self, _: &mut Str) -> ParseResult<Self, F::Output> {
        Done(self.0.build())
    }
    
    fn done(self) -> F::Output {
        self.0.build()
    }
    
}

impl<F, Ch, Str> Committed<Ch, Str> for Emit<F>
    where Str: Iterator<Item = Ch>,
          F: 'static + Copy + Factory,
{

    type Output = F::Output;
    type State = Self;

    fn init(&self, _: &mut Str) -> ParseResult<Self, F::Output> {
        Done(self.0.build())
    }
    
    fn empty(&self) -> F::Output {
        self.0.build()
    }
}

impl<T> Emit<T> {
    pub fn new(t: T) -> Self {
        Emit(t)
    }
}

// ----------- Character parsers -------------

#[derive(Copy, Clone, Debug)]
pub struct CharacterState<StaticCh>(StaticCh);

impl<StaticCh, Ch, Str> Stateful<Ch, Str> for CharacterState<StaticCh>
    where Str: Iterator<Item = Ch>,
          StaticCh: Upcast<Ch>,
{
    type Output = Ch;

    fn more(self, _: &mut Str) -> ParseResult<Self, Ch> {
        Done(self.0.upcast())
    }

    fn done(self) -> Ch {
        self.0.upcast()
    }
}
    
impl<StaticCh> CharacterState<StaticCh> {
    pub fn new(ch: StaticCh) -> Self {
        CharacterState(ch)
    }
}

pub struct Character<F>(F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<F> Copy for Character<F> where F: Copy {}
impl<F> Clone for Character<F> where F: Copy
{
    fn clone(&self) -> Self {
        Character(self.0)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<F> Debug for Character<F>
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "Character(...)")
    }
}

impl<F> Parser for Character<F> {}

impl<F, Ch, Str, StaticCh> Uncommitted<Ch, Str> for Character<F>
    where Str: PeekableIterator<Item = Ch>,
          F: Copy + Function<Ch, Output = bool>,
          Ch: ToStatic<Static = StaticCh> + Copy,
          StaticCh: 'static + Upcast<Ch>,
{
    type Output = Ch;
    type State = CharacterState<StaticCh>;
    
    fn init_maybe(&self, string: &mut Str) -> ParseResult<Self::State, Ch> {
        match string.next_if(self.0) {
            None => Backtrack,
            Some(ch) => Done(ch),
        }
    }
    
}

impl<F> Character<F> {
    pub fn new(function: F) -> Self {
        Character(function)
    }
}

pub struct CharacterRef<F>(F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<F> Copy for CharacterRef<F> where F: Copy {}
impl<F> Clone for CharacterRef<F> where F: Copy
{
    fn clone(&self) -> Self {
        CharacterRef(self.0)
    }
}

// A work around for named functions not implmenting Debug
// https://github.com/rust-lang/rust/issues/31522
impl<F> Debug for CharacterRef<F>
{
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        write!(fmt, "CharacterRef(...)")
    }
}

impl<F> Parser for CharacterRef<F> {}

impl<F, Ch, Str, StaticCh> Uncommitted<Ch, Str> for CharacterRef<F>
    where Str: PeekableIterator<Item = Ch>,
          F: Copy + for<'a> Function<&'a Ch, Output = bool>,
          Ch: ToStatic<Static = StaticCh>,
          StaticCh: 'static + Upcast<Ch>,
{
    type Output = Ch;
    type State = CharacterState<StaticCh>;
    
    fn init_maybe(&self, string: &mut Str) -> ParseResult<Self::State, Ch> {
        match string.next_if_ref(self.0) {
            None => Backtrack,
            Some(ch) => Done(ch),
        }
    }
    
}

impl<F> CharacterRef<F> {
    pub fn new(function: F) -> Self {
        CharacterRef(function)
    }
}

#[derive(Copy,Clone,Debug)]
pub struct AnyCharacter;

impl Parser for AnyCharacter {}

impl<Ch, Str> Stateful<Ch, Str> for AnyCharacter
    where Str: Iterator<Item = Ch>,
{
    type Output = Option<Ch>;

    fn more(self, string: &mut Str) -> ParseResult<Self, Option<Ch>> {
        match string.next() {
            None => Backtrack,
            Some(ch) => Done(Some(ch)),
        }
    }

    fn done(self) -> Option<Ch> {
        None
    }
}
    
impl<Ch, Str, StaticCh> Committed<Ch, Str> for AnyCharacter
    where Str: Iterator<Item = Ch>,
          Ch: ToStatic<Static = StaticCh>,
          StaticCh: 'static + Upcast<Ch>,
{
    type Output = Option<Ch>;
    type State = AnyCharacter;
    
    fn init(&self, string: &mut Str) -> ParseResult<Self::State, Option<Ch>> {
        match string.next() {
            None => Backtrack,
            Some(ch) => Done(Some(ch)),
        }
    }

    fn empty(&self) -> Option<Ch> {
        None
    }

}

// ----------- Buffering -------------

// If p is a Uncommitted<char, Chars<'a>>, then
// m.buffer() is a Uncommitted<char, Chars<'a>> with Output (char, Cow<'a,str>).
// It does as little buffering as it can, but it does allocate as buffer for the case
// where the boundary marker of the input is misaligned with that of the parser.
// For example, m is matching string literals, and the input is '"abc' followed by 'def"'
// we have to buffer up '"abc'.

// TODO(ajeffrey): make this code generic.

// TODO(ajeffrey): the output type should be Cow<'a,str> not (char, Cow<'a,str>).

#[derive(Copy, Clone, Debug)]
pub struct Buffered<P>(P);

impl<P> Parser for Buffered<P> where P: Parser {}

impl<'a, P> Uncommitted<char, Chars<'a>> for Buffered<P>
    where P: Uncommitted<char, Chars<'a>>,
{
    type Output = Cow<'a, str>;
    type State = BufferedState<P::State>;
    
    fn init_maybe(&self, string: &mut Chars<'a>) -> ParseResult<Self::State, Self::Output> {
        let string0 = string.as_str();
        match self.0.init_maybe(string) {
            Done(_) => Done(Borrowed(&string0[..(string0.len() - string.as_str().len())])),
            Continue(state) => Continue(BufferedState(state, String::from(string0))),
            Backtrack => Backtrack,
        }
    }
}

impl<P> Buffered<P> {
    pub fn new(parser: P) -> Self {
        Buffered(parser)
    }
}

#[derive(Clone,Debug)]
pub struct BufferedState<P>(P, String);

impl<'a, P> Stateful<char, Chars<'a>> for BufferedState<P>
    where P: Stateful<char, Chars<'a>>
{
    
    type Output = Cow<'a, str>;
    
    fn more(mut self, string: &mut Chars<'a>) -> ParseResult<Self, Self::Output> {
        let string0 = string.as_str();
        match self.0.more(string) {
            Backtrack => Backtrack,
            Done(_) => {
                self.1.push_str(&string0[..(string0.len() - string.as_str().len())]);
                Done(Owned(self.1))
            },
            Continue(state) => {
                self.1.push_str(string0);
                Continue(BufferedState(state, self.1))
            },
        }
    }
    
    fn done(self) -> Self::Output {
        Owned(self.1)
    }
    
}

// ----------- Parsers which are boxable -------------

#[derive(Debug)]
pub struct BoxableState<P>(Option<P>);

impl<P, Ch, Str> Boxable<Ch, Str> for BoxableState<P>
    where P: Stateful<Ch, Str>,
          Str: Iterator<Item = Ch>,
{
    type Output = P::Output;
    fn more_boxable(&mut self, string: &mut Str) -> ParseResult<(), P::Output> {
        match self.0.take().unwrap().more(string) {
            Backtrack => Backtrack,
            Done(result) => Done(result),
            Continue(state) => {
                self.0 = Some(state);
                Continue(())
            }
        }
    }
    fn done_boxable(&mut self) -> P::Output {
        self.0.take().unwrap().done()
    }
}

impl<P: ?Sized, Ch, Str, Output> Stateful<Ch, Str> for Box<P>
    where P: Boxable<Ch, Str, Output = Output>,
          Str: Iterator<Item = Ch>,
{
    type Output = Output;
    fn more(mut self, string: &mut Str) -> ParseResult<Self, Output> {
        match self.more_boxable(string) {
            Backtrack => Backtrack,
            Done(result) => Done(result),
            Continue(()) => Continue(self),
        }
    }
    fn done(mut self) -> Output {
        self.done_boxable()
    }
}

impl<P> BoxableState<P> {
    pub fn new(parser: P) -> Self {
        BoxableState(Some(parser))
    }
}

// // // ----------- Iterate over parse results -------------

// // #[derive(Copy, Clone, Debug)]
// // pub struct IterParser<P, Q, S>(P, Option<(Q, S)>);

// // impl<P, Str> Iterator for IterParser<P, P::State, Str>
// //     where P: Copy + Committed<Str>,
// //           Str: IntoPeekable,
// //           Str::Item: ToStatic,
// //           P::State: Stateful<Str>,
// // {
// //     type Item = <P::State as Stateful<Str>>::Output;
// //     fn next(&mut self) -> Option<Self::Item> {
// //         let (state, result) = match self.1.take() {
// //             None => (None, None),
// //             Some((parsing, data)) => {
// //                 match parsing.parse(data) {
// //                     Done(rest, result) => (Some((self.0.init(), rest)), Some(result)),
// //                     Continue(rest, parsing) => (Some((parsing, rest)), None),
// //                 }
// //             }
// //         };
// //         *self = IterParser(self.0, state);
// //         result
// //     }
// // }

// // impl<P, Str> IterParser<P, P::State, Str>
// //     where P: Copy + Committed<Str>,
// //           Str: IntoPeekable,
// //           Str::Item: ToStatic,
// // {
// //     pub fn new(parser: P, data: Str) -> Self {
// //         IterParser(parser, Some((parser.init(), data)))
// //     }
// // }

// // // ----------- Pipe parsers -------------

// // // TODO: restore these

// // // #[derive(Copy, Clone, Debug)]
// // // pub struct PipeStateful<P, Q, R>(P, Q, R);

// // // impl<P, Q, Str> Stateful<Str> for PipeStateful<P, P::State, Q>
// // //     where P: Copy + Committed<Str>,
// // //           Q: Stateful<Peekable<IterParser<P, P::State, Str>>>,
// // //           Str: IntoPeekable,
// // //           Str::Item: ToStatic,
// // //           P::State: Stateful<Str>,
// // // {
// // //     type Output = Q::Output;
// // //     fn parse(self, data: Str) -> ParseResult<Self, Str> {
// // //         let iterator = Peekable::new(IterParser(self.0, Some((self.1, data))));
// // //         match self.2.parse(iterator) {
// // //             Done(rest, result) => Done(rest.iter.1.unwrap().1, result),
// // //             Continue(rest, parsing2) => {
// // //                 let (parsing1, data) = rest.iter.1.unwrap();
// // //                 Continue(data, PipeStateful(self.0, parsing1, parsing2))
// // //             }
// // //         }
// // //     }
// // //     fn done(self) -> Q::Output {
// // //         // TODO: feed the output of self.1.done() into self.2.
// // //         self.1.done();
// // //         self.2.done()
// // //     }
// // // }

// // // #[derive(Copy, Clone, Debug)]
// // // pub struct PipeParser<P, Q>(P, Q);

// // // impl<P, Q, Ch> Parser<Ch> for PipeParser<P, Q>
// // //     where P: 'static + Parser<Ch>,
// // //           Q: Parser<Ch>,
// // // {
// // //     type State = PipeStateful<P,P::State,Q::State>;
// // //     type StaticOutput = Q::StaticOutput;
// // // }

// // // impl<P, Q, Str> Committed<Str> for PipeParser<P, Q>
// // //     where P: 'static + Copy + Committed<Str>,
// // //           Q: for<'a> Committed<Peekable<&'a mut IterParser<P, P::State, Str>>>,
// // //           Str: IntoPeekable,
// // //           Str::Item: ToStatic,
// // //           P::State: Stateful<Str>,
// // // {
// // //     fn init(&self) -> Self::State {
// // //         PipeStateful(self.0, self.0.init(), self.1.init())
// // //     }
// // // }

// // // impl<P, Q> PipeParser<P, Q> {
// // //     pub fn new(lhs: P, rhs: Q) -> Self {
// // //         PipeParser(lhs, rhs)
// // //     }
// // // }

