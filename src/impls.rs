//! Provide implementations of parser traits.

use super::{Parser, ParseResult};
use super::{Stateful, Committed, Uncommitted, Boxable};
use super::{Function, Consumer, Factory, PeekableIterator};
use super::{Upcast, ToStatic};
use super::ParseResult::{Done, Continue};

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

// ----------- Deal with pairs ---------------

#[derive(Copy, Clone, Debug)]
pub struct First;
impl<S, T> Function<(S, T)> for First
{
    type Output = S;
    fn apply(&self, arg: (S, T)) -> S {
        arg.0
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Second;
impl<S, T> Function<(S, T)> for Second
{
    type Output = T;
    fn apply(&self, arg: (S, T)) -> T {
        arg.1
    }
}

// ----------- Deal with units ---------------

#[derive(Copy, Clone, Debug)]
pub struct Discard;
impl<T> Function<T> for Discard
{
    type Output = ();
    fn apply(&self, _: T) -> () {
        ()
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
          F::Output: ToStatic,
{

    type StaticOutput = <F::Output as ToStatic>::Static;
    type Output = F::Output;

    fn done(self) -> F::Output {
        self.1.apply(self.0.done())
    }

    fn more(self, string: &mut Str) -> ParseResult<Self, F::Output> {
        match self.0.more(string) {
            Done(result) => Done(self.1.apply(result)),
            Continue(state) => Continue(Map(state, self.1)),
        }
    }

}

impl<P, F, Ch, Str> Committed<Ch, Str> for Map<P, F>
    where P: Committed<Ch, Str>,
          F: 'static + Copy + Function<<P::State as Stateful<Ch, Str>>::Output>,
          F::Output: ToStatic,
{

    fn empty(&self) -> F::Output {
        self.1.apply(self.0.empty())
    }

}

impl<P, F, Ch, Str> Uncommitted<Ch, Str> for Map<P, F>
    where P: Uncommitted<Ch, Str>,
          F: 'static + Copy + Function<<P::State as Stateful<Ch, Str>>::Output>,
          F::Output: ToStatic,
{

    type State = Map<P::State, F>;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, F::Output>> {
        match self.0.init(string) {
            None => None,
            Some(Done(result)) => Some(Done(self.1.apply(result))),
            Some(Continue(state)) => Some(Continue(Map(state, self.1))),
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

impl<P, Q, Ch, Str> Committed<Ch, Str> for AndThen<P, Q>
    where P: Committed<Ch, Str>,
          Q: 'static + Copy + Committed<Ch, Str>,
{

    fn empty(&self) -> <Self::State as Stateful<Ch, Str>>::Output {
        (self.0.empty(), self.1.empty())
    }

}

impl<P, Q, Ch, Str> Uncommitted<Ch, Str> for AndThen<P, Q>
    where P: Uncommitted<Ch, Str>,
          Q: 'static + Copy + Committed<Ch, Str>,
{

    type State = AndThenState<P::State, Q, <P::State as Stateful<Ch, Str>>::StaticOutput, Q::State>;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, <Self::State as Stateful<Ch, Str>>::Output>> {
        match self.0.init(string) {
            None => None,
            Some(Done(fst)) => match self.1.init(string) {
                None => Some(Continue(InBetween(fst.to_static(), self.1))),
                Some(Done(snd)) => Some(Done((fst, snd))),
                Some(Continue(snd)) => Some(Continue(InRhs(fst.to_static(), snd))),
            },
            Some(Continue(fst)) => Some(Continue(InLhs(fst, self.1))),
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

impl<PState, Q, Ch, Str> Stateful<Ch, Str> for AndThenState<PState, Q, PState::StaticOutput, Q::State>
    where PState: Stateful<Ch, Str>,
          Q: Committed<Ch, Str>,
{

    type StaticOutput = (PState::StaticOutput, <Q::State as Stateful<Ch, Str>>::StaticOutput);
    type Output = (PState::Output, <Q::State as Stateful<Ch, Str>>::Output);

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
                        None => Continue(InBetween(fst.to_static(), snd)),
                        Some(Done(snd)) => Done((fst, snd)),
                        Some(Continue(snd)) => Continue(InRhs(fst.to_static(), snd)),
                    },
                    Continue(fst) => Continue(InLhs(fst, snd)),
                }
            }
            InBetween(fst, snd) => {
                match snd.init(string) {
                    None => Continue(InBetween(fst, snd)),
                    Some(Done(snd)) => Done((fst.upcast(), snd)),
                    Some(Continue(snd)) => Continue(InRhs(fst, snd)),
                }
            }
            InRhs(fst, snd) => {
                match snd.more(string) {
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
          Q: Committed<Ch, Str>,
          Q::State: Stateful<Ch, Str, StaticOutput = <P::State as Stateful<Ch, Str>>::StaticOutput, Output = <P::State as Stateful<Ch, Str>>::Output>,
{

    fn empty(&self) -> <P::State as Stateful<Ch, Str>>::Output {
        self.1.empty()
    }

}

impl<P, Q, Ch, Str> Uncommitted<Ch, Str> for OrElse<P, Q>
    where P: Uncommitted<Ch, Str>,
          Q: Uncommitted<Ch, Str>,
          Q::State: Stateful<Ch, Str, StaticOutput = <P::State as Stateful<Ch, Str>>::StaticOutput, Output = <P::State as Stateful<Ch, Str>>::Output>,
{

    type State = OrElseState<P::State, Q::State>;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, <Self::State as Stateful<Ch, Str>>::Output>> {
        match self.0.init(string) {
            Some(Done(result)) => Some(Done(result)),
            Some(Continue(lhs)) => Some(Continue(Lhs(lhs))),
            None => match self.1.init(string) {
                Some(Done(result)) => Some(Done(result)),
                Some(Continue(rhs)) => Some(Continue(Rhs(rhs))),
                None => None,
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
          Q: Stateful<Ch, Str, StaticOutput = P::StaticOutput, Output = P::Output>,
{
    type StaticOutput = P::StaticOutput;
    type Output = P::Output;

    fn more(self, string: &mut Str) -> ParseResult<Self, P::Output> {
        match self {
            Lhs(lhs) => match lhs.more(string) {
                Done(result) => Done(result),
                Continue(lhs) => Continue(Lhs(lhs)),
            },
            Rhs(rhs) => match rhs.more(string) {
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

impl<P, T, Ch, Str> Stateful<Ch, Str> for StarState<P, P::State, T>
    where P: Copy + Uncommitted<Ch, Str>,
          T: ToStatic + Consumer<<P::State as Stateful<Ch, Str>>::Output>,
          Str: PeekableIterator,
{
    type StaticOutput = T::Static;
    type Output = T;
    fn more(mut self, string: &mut Str) -> ParseResult<Self, T> {
        loop {
            match self.1.take() {
                None => {
                    match self.0.init(string) {
                        Some(Continue(state)) => return Continue(StarState(self.0, Some(state), self.2)),
                        Some(Done(result)) => self.2.accept(result),
                        None => return if string.is_empty() {
                            Continue(self)
                        } else {
                            Done(self.2)
                        },
                    }
                }
                Some(state) => {
                    match state.more(string) {
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
          Str: PeekableIterator,
          F::Output: ToStatic + Consumer<<P::State as Stateful<Ch, Str>>::Output>,
{
    type State = StarState<P, P::State, F::Output>;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, F::Output>> {
        match self.0.init(string) {
            None => None,
            Some(Continue(state)) => Some(Continue(StarState(self.0, Some(state), self.1.build()))),
            Some(Done(result)) => {
                let mut buffer = self.1.build();
                buffer.accept(result);
                Some(StarState(self.0, None, buffer).more(string))
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

impl<P, F, Ch, Str> Uncommitted<Ch, Str> for Star<P, F>
    where P: 'static + Copy + Uncommitted<Ch, Str>,
          F: 'static + Factory,
          Str: PeekableIterator,
          F::Output: ToStatic + Consumer<<P::State as Stateful<Ch, Str>>::Output>,
{

    type State = StarState<P, P::State, F::Output>;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, F::Output>> {
        if string.is_empty() {
            None
        } else {
            Some(StarState(self.0, None, self.1.build()).more(string))
        }
    }

}

impl<P, F, Ch, Str> Committed<Ch, Str> for Star<P, F>
    where P: 'static + Copy + Uncommitted<Ch, Str>,
          F: 'static + Factory,
          Str: PeekableIterator,
          F::Output: ToStatic + Consumer<<P::State as Stateful<Ch, Str>>::Output>,
{

    fn empty(&self) -> F::Output {
        self.1.build()
    }

}

impl<P, F> Star<P, F> {
    pub fn new(parser: P, factory: F) -> Self {
        Star(parser, factory)
    }
}

// ----------- Optional parse -------------

#[derive(Copy, Clone, Debug)]
pub struct Opt<P>(P);

impl<P> Parser for Opt<P> where P: Parser {}

impl<P, Ch, Str> Stateful<Ch, Str> for Opt<P>
    where P: Stateful<Ch, Str>,
{

    type StaticOutput = Option<P::StaticOutput>;
    type Output = Option<P::Output>;

    fn more(self, string: &mut Str) -> ParseResult<Self, Self::Output> {
        match self.0.more(string) {
            Done(result) => Done(Some(result)),
            Continue(parsing) => Continue(Opt(parsing)),
        }
    }

    fn done(self) -> Self::Output {
        Some(self.0.done())
    }

}

impl<P, Ch, Str> Uncommitted<Ch, Str> for Opt<P>
    where Str: PeekableIterator,
          P: Uncommitted<Ch, Str>,
{

    type State = Opt<P::State>;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, <Self::State as Stateful<Ch, Str>>::Output>> {
        match self.0.init(string) {
            None => if string.is_empty() {
                None
            } else {
                Some(Done(None))
            },
            Some(Done(result)) => Some(Done(Some(result))),
            Some(Continue(parsing)) => Some(Continue(Opt(parsing))),
        }
    }

}

impl<P, Ch, Str> Committed<Ch, Str> for Opt<P>
    where Str: PeekableIterator,
          P: Uncommitted<Ch, Str>,
{

    fn empty(&self) -> <Self::State as Stateful<Ch, Str>>::Output {
        None
    }

}

impl<P> Opt<P> {
    pub fn new(parser: P) -> Self {
        Opt(parser)
    }
}

// ----------- A type for parsers which immediately emit a result -------------

#[derive(Copy, Clone, Debug)]
pub struct Emit<F>(F);

impl<F> Parser for Emit<F> {}

impl<F, Ch, Str> Stateful<Ch, Str> for Emit<F>
    where F: Factory,
          F::Output: ToStatic,
{

    type StaticOutput = <F::Output as ToStatic>::Static;
    type Output = F::Output;

    fn more(self, _: &mut Str) -> ParseResult<Self, F::Output> {
        Done(self.0.build())
    }

    fn done(self) -> F::Output {
        self.0.build()
    }

}

impl<F, Ch, Str> Uncommitted<Ch, Str> for Emit<F>
    where Str: PeekableIterator,
          F: 'static + Copy + Factory,
          F::Output: ToStatic,
{

    type State = Self;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self, F::Output>> {
        if string.is_empty() {
            None
        } else {
            Some(Done(self.0.build()))
        }
    }

}

impl<F, Ch, Str> Committed<Ch, Str> for Emit<F>
    where Str: PeekableIterator,
          F: 'static + Copy + Factory,
          F::Output: ToStatic,
{

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
pub enum CharacterState {}

impl<Ch, Str> Stateful<Ch, Str> for CharacterState
    where Ch: ToStatic,
{

    type StaticOutput = Ch::Static;
    type Output = Ch;

    fn more(self, _: &mut Str) -> ParseResult<Self, Ch> { 
        match self {}
   }

    fn done(self) -> Ch {
        match self {}
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

impl<F, Ch, Str> Uncommitted<Ch, Str> for Character<F>
    where Str: PeekableIterator<Item = Ch>,
          F: Copy + Function<Ch, Output = bool>,
          Ch: Copy + ToStatic,
{
    type State = CharacterState;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, Ch>> {
        match string.next_if(self.0) {
            None => None,
            Some(ch) => Some(Done(ch)),
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

impl<F, Ch, Str> Uncommitted<Ch, Str> for CharacterRef<F>
    where Str: PeekableIterator<Item = Ch>,
          F: Copy + for<'a> Function<&'a Ch, Output = bool>,
          Ch: ToStatic,
{
    type State = CharacterState;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, Ch>> {
        match string.next_if_ref(self.0) {
            None => None,
            Some(ch) => Some(Done(ch)),
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
          Ch: ToStatic,
{
    type StaticOutput = Option<Ch::Static>;
    type Output = Option<Ch>;

    fn more(self, string: &mut Str) -> ParseResult<Self, Option<Ch>> {
        match string.next() {
            None => Continue(self),
            Some(ch) => Done(Some(ch)),
        }
    }

    fn done(self) -> Option<Ch> {
        None
    }
}

impl<Ch, Str> Uncommitted<Ch, Str> for AnyCharacter
    where Str: Iterator<Item = Ch>,
          Ch: ToStatic,
{
    type State = AnyCharacter;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, Option<Ch>>> {
        match string.next() {
            None => None,
            Some(ch) => Some(Done(Some(ch))),
        }
    }

}

impl<Ch, Str> Committed<Ch, Str> for AnyCharacter
    where Str: Iterator<Item = Ch>,
          Ch: ToStatic,
{

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

#[derive(Copy, Clone, Debug)]
pub struct Buffered<P>(P);

impl<P> Parser for Buffered<P> where P: Parser {}

impl<'a, P> Uncommitted<char, Chars<'a>> for Buffered<P>
    where P: Uncommitted<char, Chars<'a>>,
{
    type State = BufferedState<P::State>;

    fn init(&self, string: &mut Chars<'a>) -> Option<ParseResult<Self::State, Cow<'a, str>>> {
        let string0 = string.as_str();
        match self.0.init(string) {
            Some(Done(_)) => Some(Done(Borrowed(&string0[..(string0.len() - string.as_str().len())]))),
            Some(Continue(state)) => Some(Continue(BufferedState(state, String::from(string0)))),
            None => None,
        }
    }
}

impl<'a, P> Committed<char, Chars<'a>> for Buffered<P>
    where P: Committed<char, Chars<'a>>,
{
    fn empty(&self) -> Cow<'a, str> { Borrowed("") }
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

    type StaticOutput = Cow<'static, str>;
    type Output = Cow<'a, str>;

    fn more(mut self, string: &mut Chars<'a>) -> ParseResult<Self, Self::Output> {
        let string0 = string.as_str();
        match self.0.more(string) {
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
{
    type StaticOutput = P::StaticOutput;
    type Output = P::Output;
    fn more_boxable(&mut self, string: &mut Str) -> ParseResult<(), P::Output> {
        match self.0.take().unwrap().more(string) {
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

impl<P: ?Sized, Ch, Str> Stateful<Ch, Str> for Box<P>
    where P: Boxable<Ch, Str>,
{
    type StaticOutput = P::StaticOutput;
    type Output = P::Output;
    fn more(mut self, string: &mut Str) -> ParseResult<Self, P::Output> {
        match self.more_boxable(string) {
            Done(result) => Done(result),
            Continue(()) => Continue(self),
        }
    }
    fn done(mut self) -> P::Output {
        self.done_boxable()
    }
}

impl<P> BoxableState<P> {
    pub fn new(parser: P) -> Self {
        BoxableState(Some(parser))
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Boxed<P, F>(P, F);

impl<P, F> Parser for Boxed<P, F> where P: Parser {}

impl<P, F, Ch, Str> Uncommitted<Ch, Str> for Boxed<P, F>
    where P: Uncommitted<Ch, Str>,
          F: Function<BoxableState<P::State>>,
          F::Output: 'static + Stateful<Ch, Str, StaticOutput = <P::State as Stateful<Ch, Str>>::StaticOutput, Output = <P::State as Stateful<Ch, Str>>::Output>,
{
    type State = F::Output;

    fn init(&self, string: &mut Str) -> Option<ParseResult<Self::State, <P::State as Stateful<Ch, Str>>::Output>> {
        match self.0.init(string) {
            None => None,
            Some(Done(result)) => Some(Done(result)),
            Some(Continue(parsing)) => Some(Continue(self.1.apply(BoxableState::new(parsing)))),
        }
    }
}

impl<P, F, Ch, Str> Committed<Ch, Str> for Boxed<P, F>
    where P: Committed<Ch, Str>,
          F: Function<BoxableState<P::State>>,
          F::Output: 'static + Stateful<Ch, Str, StaticOutput = <P::State as Stateful<Ch, Str>>::StaticOutput, Output = <P::State as Stateful<Ch, Str>>::Output>,
{
    fn empty(&self) -> <P::State as Stateful<Ch, Str>>::Output {
        self.0.empty()
    }
}

impl<P, F> Boxed<P, F> {
    pub fn new(parser: P, function: F) -> Self {
        Boxed(parser, function)
    }
}

// // ----------- Iterate over parse results -------------

// #[derive(Copy, Clone, Debug)]
// pub struct IterParser<P, Q, S>(P, Option<(Q, S)>);

// impl<P, Str> Iterator for IterParser<P, P::State, Str>
//     where P: Copy + Committed<Str>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
// {
//     type Item = <P::State as Stateful<Str>>::Output;
//     fn next(&mut self) -> Option<Self::Item> {
//         let (state, result) = match self.1.take() {
//             None => (None, None),
//             Some((parsing, data)) => {
//                 match parsing.parse(data) {
//                     Done(rest, result) => (Some((self.0.init(), rest)), Some(result)),
//                     Continue(rest, parsing) => (Some((parsing, rest)), None),
//                 }
//             }
//         };
//         *self = IterParser(self.0, state);
//         result
//     }
// }

// impl<P, Str> IterParser<P, P::State, Str>
//     where P: Copy + Committed<Str>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
// {
//     pub fn new(parser: P, data: Str) -> Self {
//         IterParser(parser, Some((parser.init(), data)))
//     }
// }

// // ----------- Pipe parsers -------------

// TODO: restore these

// #[derive(Copy, Clone, Debug)]
// pub struct PipeStateful<P, Q, R>(P, Q, R);

// impl<P, Q, Str> Stateful<Str> for PipeStateful<P, P::State, Q>
//     where P: Copy + Committed<Str>,
//           Q: Stateful<Peekable<IterParser<P, P::State, Str>>>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
// {
//     type Output = Q::Output;
//     fn parse(self, data: Str) -> ParseResult<Self, Str> {
//         let iterator = Peekable::new(IterParser(self.0, Some((self.1, data))));
//         match self.2.parse(iterator) {
//             Done(rest, result) => Done(rest.iter.1.unwrap().1, result),
//             Continue(rest, parsing2) => {
//                 let (parsing1, data) = rest.iter.1.unwrap();
//                 Continue(data, PipeStateful(self.0, parsing1, parsing2))
//             }
//         }
//     }
//     fn done(self) -> Q::Output {
//         // TODO: feed the output of self.1.done() into self.2.
//         self.1.done();
//         self.2.done()
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct PipeParser<P, Q>(P, Q);

// impl<P, Q, Ch> Parser<Ch> for PipeParser<P, Q>
//     where P: 'static + Parser<Ch>,
//           Q: Parser<Ch>,
// {
//     type State = PipeStateful<P,P::State,Q::State>;
//     type StaticOutput = Q::StaticOutput;
// }

// impl<P, Q, Str> Committed<Str> for PipeParser<P, Q>
//     where P: 'static + Copy + Committed<Str>,
//           Q: for<'a> Committed<Peekable<&'a mut IterParser<P, P::State, Str>>>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
// {
//     fn init(&self) -> Self::State {
//         PipeStateful(self.0, self.0.init(), self.1.init())
//     }
// }

// impl<P, Q> PipeParser<P, Q> {
//     pub fn new(lhs: P, rhs: Q) -> Self {
//         PipeParser(lhs, rhs)
//     }
// }

