//! Provide implementations of parser traits.

use super::{Parser, ParseResult};
use super::{Stateful, Committed, Uncommitted, Boxable};
use super::{InferOutput, StatefulInfer, CommittedInfer, UncommittedInfer};
use super::{Function, Consumer, Factory, PeekableIterator};
use super::{Upcast, ToStatic, StaticMarker};
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

impl<P1, P2, F> Upcast<Map<P2, F>> for Map<P1, F>
    where P1: Upcast<P2>
{
    fn upcast(self) -> Map<P2, F> {
        Map(self.0.upcast(), self.1)
    }
}

impl<P, F> ToStatic for Map<P, F>
    where P: ToStatic,
          F: 'static,
{
    type Static = Map<P::Static, F>;
    fn to_static(self) -> Self::Static {
        Map(self.0.to_static(), self.1)
    }
}

impl<P, F, Input> InferOutput<Input> for Map<P, F>
    where P: InferOutput<Input>,
          F: Function<P::Output>,
{
    type Output = F::Output;
}

impl<P, F> Parser for Map<P, F> {}

impl<P, F, Input> Stateful<Input, F::Output> for Map<P, F>
    where P: StatefulInfer<Input>,
          F: Function<P::Output>,
{

    fn done(self) -> F::Output {
        self.1.apply(self.0.done())
    }

    fn more(self, data: &mut Input) -> ParseResult<Self, F::Output> {
        match self.0.more(data) {
            Done(result) => Done(self.1.apply(result)),
            Continue(state) => Continue(Map(state, self.1)),
        }
    }

}

impl<P, F, Input> Committed<Input, F::Output> for Map<P, F>
    where P: CommittedInfer<Input>,
          F: Copy + Function<P::Output>,
{

    fn empty(&self) -> F::Output {
        self.1.apply(self.0.empty())
    }

}

impl<P, F, Input> Uncommitted<Input, F::Output> for Map<P, F>
    where P: UncommittedInfer<Input>,
          F: Copy + Function<P::Output>,
{

    type State = Map<P::State, F>;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, F::Output>> {
        match self.0.init(data) {
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

impl<P, Q, Input> InferOutput<Input> for AndThen<P, Q>
    where P: InferOutput<Input>,
          Q: InferOutput<Input>,
{
    type Output = (P::Output, Q::Output);
}

impl<P, Q> Parser for AndThen<P, Q> {}

impl<P, Q, Input, POutput, QOutput> Committed<Input, (POutput, QOutput)> for AndThen<P, Q>
    where P: Committed<Input, POutput>,
          Q: Copy + Committed<Input, QOutput>,
{

    fn empty(&self) -> (POutput, QOutput) {
        (self.0.empty(), self.1.empty())
    }

}

impl<P, Q, Input, POutput, QOutput> Uncommitted<Input, (POutput, QOutput)> for AndThen<P, Q>
    where P: Uncommitted<Input, POutput>,
          Q: Copy + Committed<Input, QOutput>,
{

    type State = AndThenState<P::State, POutput, Q, Q::State>;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, (POutput, QOutput)>> {
        match self.0.init(data) {
            None => None,
            Some(Done(fst)) => match self.1.init(data) {
                None => Some(Continue(InBetween(fst, self.1))),
                Some(Done(snd)) => Some(Done((fst, snd))),
                Some(Continue(snd)) => Some(Continue(InRhs(fst, snd))),
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
pub enum AndThenState<PState, POutput, Q, QState> {
    InLhs(PState, Q),
    InBetween(POutput, Q),
    InRhs(POutput, QState),
}

impl<PState1, PState2, POutput1, POutput2, Q, QState1, QState2> Upcast<AndThenState<PState2, POutput2, Q, QState2>> for AndThenState<PState1, POutput1, Q, QState1>
    where PState1: Upcast<PState2>,
          POutput1: Upcast<POutput2>,
          QState1: Upcast<QState2>,
{
    fn upcast(self) -> AndThenState<PState2, POutput2, Q, QState2> {
        match self {
            InLhs(fst, snd) => InLhs(fst.upcast(), snd),
            InBetween(fst, snd) => InBetween(fst.upcast(), snd),
            InRhs(fst, snd) => InRhs(fst.upcast(), snd.upcast()),
        }
    }
}

impl<PState, POutput, Q, QState> ToStatic for AndThenState<PState, POutput, Q, QState>
    where PState: ToStatic,
          POutput: ToStatic,
          Q: 'static,
          QState: ToStatic,
{
    type Static = AndThenState<PState::Static, POutput::Static, Q, QState::Static>;
    fn to_static(self) -> Self::Static {
        match self {
            InLhs(fst, snd) => InLhs(fst.to_static(), snd),
            InBetween(fst, snd) => InBetween(fst.to_static(), snd),
            InRhs(fst, snd) => InRhs(fst.to_static(), snd.to_static()),
        }
    }
}

impl<PState, POutput, Q, QState, Input> InferOutput<Input> for AndThenState<PState, POutput, Q, QState>
    where PState: InferOutput<Input>,
          QState: InferOutput<Input>,
{
    type Output = (PState::Output, QState::Output);
}

impl<PState, POutput1, POutput2, Q, QOutput, Input> Stateful<Input, (POutput2, QOutput)> for AndThenState<PState, POutput1, Q, Q::State>
    where PState: Stateful<Input, POutput1>,
          Q: Committed<Input, QOutput>,
          Q::State: Stateful<Input, QOutput>,
          POutput1: Upcast<POutput2>,
{

    fn done(self) -> (POutput2, QOutput)
    {
        match self {
            InLhs(fst, snd) => (fst.done().upcast(), snd.empty()),
            InBetween(fst, snd) => (fst.upcast(), snd.empty()),
            InRhs(fst, snd) => (fst.upcast(), snd.done()),
        }
    }

    fn more(self, data: &mut Input) -> ParseResult<Self, (POutput2, QOutput)>
    {
        match self {
            InLhs(fst, snd) => {
                match fst.more(data) {
                    Done(fst) => match snd.init(data) {
                        None => Continue(InBetween(fst, snd)),
                        Some(Done(snd)) => Done((fst.upcast(), snd)),
                        Some(Continue(snd)) => Continue(InRhs(fst, snd)),
                    },
                    Continue(fst) => Continue(InLhs(fst, snd)),
                }
            }
            InBetween(fst, snd) => {
                match snd.init(data) {
                    None => Continue(InBetween(fst, snd)),
                    Some(Done(snd)) => Done((fst.upcast(), snd)),
                    Some(Continue(snd)) => Continue(InRhs(fst, snd)),
                }
            }
            InRhs(fst, snd) => {
                match snd.more(data) {
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

impl<P, Q, Input> InferOutput<Input> for OrElse<P, Q>
    where P: InferOutput<Input>,
          Q: InferOutput<Input>,
{
    type Output = P::Output;
}

impl<P, Q> Parser for OrElse<P, Q> {}

impl<P, Q, Input, Output> Committed<Input, Output> for OrElse<P, Q>
    where P: Uncommitted<Input, Output>,
          Q: Committed<Input, Output>,
{

    fn empty(&self) -> Output {
        self.1.empty()
    }

}

impl<P, Q, Input, Output> Uncommitted<Input, Output> for OrElse<P, Q>
    where P: Uncommitted<Input, Output>,
          Q: Uncommitted<Input, Output>,
{

    type State = OrElseState<P::State, Q::State>;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, Output>> {
        match self.0.init(data) {
            Some(Done(result)) => Some(Done(result)),
            Some(Continue(lhs)) => Some(Continue(Lhs(lhs))),
            None => match self.1.init(data) {
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

impl<P1, P2, Q1, Q2> Upcast<OrElseState<P2, Q2>> for OrElseState<P1, Q1>
    where P1: Upcast<P2>,
          Q1: Upcast<Q2>,
{
    fn upcast(self) -> OrElseState<P2, Q2> {
        match self {
            Lhs(lhs) => Lhs(lhs.upcast()),
            Rhs(rhs) => Rhs(rhs.upcast()),
        }
    }
}

impl<P, Q> ToStatic for OrElseState<P, Q>
    where P: ToStatic,
          Q: ToStatic,
{
    type Static = OrElseState<P::Static, Q::Static>;
    fn to_static(self) -> Self::Static {
        match self {
            Lhs(lhs) => Lhs(lhs.to_static()),
            Rhs(rhs) => Rhs(rhs.to_static()),
        }
    }
}

impl<P, Q, Input> InferOutput<Input> for OrElseState<P, Q>
    where P: InferOutput<Input>,
{
    type Output = P::Output;
}

impl<P, Q, Input, Output> Stateful<Input, Output> for OrElseState<P, Q>
    where P: Stateful<Input, Output>,
          Q: Stateful<Input, Output>,
{
    fn more(self, data: &mut Input) -> ParseResult<Self, Output> {
        match self {
            Lhs(lhs) => match lhs.more(data) {
                Done(result) => Done(result),
                Continue(lhs) => Continue(Lhs(lhs)),
            },
            Rhs(rhs) => match rhs.more(data) {
                Done(result) => Done(result),
                Continue(rhs) => Continue(Rhs(rhs)),
            },
        }
    }

    fn done(self) -> Output {
        match self {
            Lhs(lhs) => lhs.done(),
            Rhs(rhs) => rhs.done(),
        }
    }

}

// ----------- Kleene star ---------------

#[derive(Clone,Debug)]
pub struct StarState<P, PState, Output>(P, Option<PState>, Output);

impl<P, PState1, PState2, Output1, Output2> Upcast<StarState<P, PState2, Output2>> for StarState<P, PState1, Output1>
    where PState1: Upcast<PState2>,
          Output1: Upcast<Output2>,
{
    fn upcast(self) -> StarState<P, PState2, Output2> {
        StarState(self.0, self.1.upcast(), self.2.upcast())
    }
}

impl<P, PState, Output> ToStatic for StarState<P, PState, Output>
    where P: 'static,
          PState: ToStatic,
          Output: ToStatic,
{
    type Static = StarState<P, PState::Static, Output::Static>;
    fn to_static(self) -> Self::Static {
        StarState(self.0, self.1.to_static(), self.2.to_static())
    }
}

impl<P, PState, Input, Output> InferOutput<Input> for StarState<P, PState, Output>
{
    type Output = Output;
}

impl<P, Input, Output> Stateful<Input, Output> for StarState<P, P::State, Output>
    where P: Copy + UncommittedInfer<Input>,
          P::State: Stateful<Input, <P as InferOutput<Input>>::Output>,
          Input: PeekableIterator,
          Output: Consumer<P::Output>,
{
    fn more(mut self, data: &mut Input) -> ParseResult<Self, Output> {
        loop {
            match self.1.take() {
                None => {
                    match self.0.init(data) {
                        Some(Continue(state)) => return Continue(StarState(self.0, Some(state), self.2)),
                        Some(Done(result)) => self.2.accept(result),
                        None => return if data.is_empty() {
                            Continue(self)
                        } else {
                            Done(self.2)
                        },
                    }
                }
                Some(state) => {
                    match state.more(data) {
                        Continue(state) => return Continue(StarState(self.0, Some(state), self.2)),
                        Done(result) => self.2.accept(result),
                    }
                }
            }
        }
    }
    fn done(self) -> Output {
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

impl<P, F, Input> InferOutput<Input> for Plus<P, F>
    where P: InferOutput<Input>,
          F: Factory,
{
    type Output = F::Output;
}

impl<P, F> Parser for Plus<P, F> {}

impl<P, F, Input> Uncommitted<Input, F::Output> for Plus<P, F>
    where P: Copy + UncommittedInfer<Input>,
          F: Factory,
          Input: PeekableIterator,
          P::State: Stateful<Input, <P as InferOutput<Input>>::Output>,
          F::Output: Consumer<P::Output>,
{
    type State = StarState<P, P::State, F::Output>;

    fn init(&self, data: &mut Input) -> Option<ParseResult<StarState<P, P::State, F::Output>, F::Output>> {
        match self.0.init(data) {
            None => None,
            Some(Continue(state)) => Some(Continue(StarState(self.0, Some(state), self.1.build()))),
            Some(Done(result)) => {
                let mut buffer = self.1.build();
                buffer.accept(result);
                Some(StarState(self.0, None, buffer).more(data))
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

impl<P, F, Input> InferOutput<Input> for Star<P, F>
    where P: InferOutput<Input>,
          F: Factory,
{
    type Output = F::Output;
}

impl<P, F> Parser for Star<P, F> {}

impl<P, F, Input> Uncommitted<Input, F::Output> for Star<P, F>
    where P: Copy + UncommittedInfer<Input>,
          F: Factory,
          Input: PeekableIterator,
          P::State: Stateful<Input, <P as InferOutput<Input>>::Output>,
          F::Output: Consumer<P::Output>,
{
    type State = StarState<P, P::State, F::Output>;

    fn init(&self, data: &mut Input) -> Option<ParseResult<StarState<P, P::State, F::Output>, F::Output>> {
        if data.is_empty() {
            None
        } else {
            Some(StarState(self.0, None, self.1.build()).more(data))
        }
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

impl<P1, P2> Upcast<Opt<P2>> for Opt<P1>
    where P1: Upcast<P2>,
{
    fn upcast(self) -> Opt<P2> {
        Opt(self.0.upcast())
    }
}

impl<P> ToStatic for Opt<P>
    where P: ToStatic,
{
    type Static = Opt<P::Static>;
    fn to_static(self) -> Self::Static {
        Opt(self.0.to_static())
    }
}

impl<P, Input> InferOutput<Input> for Opt<P>
    where P: InferOutput<Input>,
{
    type Output = Option<P::Output>;
}

impl<P> Parser for Opt<P> where P: Parser {}

impl<P, Input, Output> Stateful<Input, Option<Output>> for Opt<P>
    where P: Stateful<Input, Output>,
{
    fn more(self, data: &mut Input) -> ParseResult<Self, Option<Output>> {
        match self.0.more(data) {
            Done(result) => Done(Some(result)),
            Continue(parsing) => Continue(Opt(parsing)),
        }
    }

    fn done(self) -> Option<Output> {
        Some(self.0.done())
    }
}

impl<P, Input, Output> Uncommitted<Input, Option<Output>> for Opt<P>
    where P: Uncommitted<Input, Output>,
          Input: PeekableIterator,
{
    type State = Opt<P::State>;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, Option<Output>>> {
        match self.0.init(data) {
            None => if data.is_empty() {
                None
            } else {
                Some(Done(None))
            },
            Some(Done(result)) => Some(Done(Some(result))),
            Some(Continue(parsing)) => Some(Continue(Opt(parsing))),
        }
    }

}

impl<P, Input, Output> Committed<Input, Option<Output>> for Opt<P>
    where P: Committed<Input, Output>,
          Input: PeekableIterator,
{

    fn empty(&self) -> Option<Output> {
        None
    }

}

impl<P> Opt<P> {
    pub fn new(parser: P) -> Self {
        Opt(parser)
    }
}

// ----------- A type for parsers which don't exist -------------

#[derive(Copy, Clone, Debug)]
pub enum Impossible {}

impl StaticMarker for Impossible {}

impl<Input, Output> Stateful<Input, Output> for Impossible
{
    fn more(self, _: &mut Input) -> ParseResult<Self, Output> { 
        match self {}
    }

    fn done(self) -> Output {
        match self {}
    }
}


// ----------- A type for parsers which immediately emit a result -------------

#[derive(Copy, Clone, Debug)]
pub struct Emit<F>(F);

impl<F, Input> InferOutput<Input> for Emit<F>
    where F: Factory,
{
    type Output = F::Output;
}

impl<F> Parser for Emit<F> {}

impl<F, Input> Uncommitted<Input, F::Output> for Emit<F>
    where Input: PeekableIterator,
          F: Copy + Factory,
{
    type State = Impossible;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, F::Output>> {
        if data.is_empty() {
            None
        } else {
            Some(Done(self.0.build()))
        }
    }

}

impl<F, Input> Committed<Input, F::Output> for Emit<F>
    where Input: PeekableIterator,
          F: Copy + Factory,
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

impl<F, Input> InferOutput<Input> for Character<F>
    where Input: Iterator,
{
    type Output = Input::Item;
}

impl<F> Parser for Character<F> {}

impl<F, Input> Uncommitted<Input, Input::Item> for Character<F>
    where Input: PeekableIterator,
          F: Copy + Function<Input::Item, Output = bool>,
          Input::Item: Copy,
{
    type State = Impossible;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, Input::Item>> {
        match data.next_if(self.0) {
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

impl<F, Input> InferOutput<Input> for CharacterRef<F>
    where Input: Iterator,
{
    type Output = Input::Item;
}

impl<F> Parser for CharacterRef<F> {}

impl<F, Input> Uncommitted<Input, Input::Item> for CharacterRef<F>
    where Input: PeekableIterator,
          F: Copy + for<'a> Function<&'a Input::Item, Output = bool>,
{
    type State = Impossible;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, Input::Item>> {
        match data.next_if_ref(self.0) {
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

impl<Input> InferOutput<Input> for AnyCharacter
    where Input: Iterator,
{
    type Output = Option<Input::Item>;
}

impl<Input> Stateful<Input, Option<Input::Item>> for AnyCharacter
    where Input: Iterator,
{
    fn more(self, data: &mut Input) -> ParseResult<Self, Option<Input::Item>> {
        match data.next() {
            None => Continue(self),
            Some(item) => Done(Some(item)),
        }
    }

    fn done(self) -> Option<Input::Item> {
        None
    }
}


impl<Input> Uncommitted<Input, Option<Input::Item>> for AnyCharacter
    where Input: Iterator,
{
    type State = Impossible;

    fn init(&self, data: &mut Input) -> Option<ParseResult<Self::State, Option<Input::Item>>> {
        match data.next() {
            None => None,
            Some(item) => Some(Done(Some(item))),
        }
    }
}

impl<Input> Committed<Input, Option<Input::Item>> for AnyCharacter
    where Input: Iterator,
{
    fn empty(&self) -> Option<Input::Item> {
        None
    }
}

// ----------- Buffering -------------

// If p is a Uncommitted<Chars<'a>, Output>, then
// m.buffer() is a Uncommitted<Chars<'a>, Cow<'a, str>>.
//
// It does as little buffering as it can, but it does allocate as buffer for the case
// where the boundary marker of the input is misaligned with that of the parser.
// For example, m is matching string literals, and the input is '"abc' followed by 'def"'
// we have to buffer up '"abc'.

// TODO(ajeffrey): make this code generic.

#[derive(Copy, Clone, Debug)]
pub struct Buffered<P>(P);

impl<'a, P> InferOutput<Chars<'a>> for Buffered<P>
    where P: InferOutput<Chars<'a>>
{
    type Output = Cow<'a, str>;
}

impl<P> Parser for Buffered<P> where P: Parser {}

impl<'a, P> Uncommitted<Chars<'a>, Cow<'a, str>> for Buffered<P>
    where P: UncommittedInfer<Chars<'a>>
{
    type State = BufferedState<P::State>;

    fn init(&self, data: &mut Chars<'a>) -> Option<ParseResult<Self::State, Cow<'a, str>>> {
        let string = data.as_str();
        match self.0.init(data) {
            Some(Done(_)) => Some(Done(Borrowed(&string[..(string.len() - data.as_str().len())]))),
            Some(Continue(state)) => Some(Continue(BufferedState(state, String::from(string)))),
            None => None,
        }
    }
}

impl<'a, P> Committed<Chars<'a>, Cow<'a, str>> for Buffered<P>
    where P: CommittedInfer<Chars<'a>>
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

impl<P1, P2> Upcast<BufferedState<P2>> for BufferedState<P1>
    where P1: Upcast<P2>
{
    fn upcast(self) -> BufferedState<P2> {
        BufferedState(self.0.upcast(), self.1)
    }
}

impl<P> ToStatic for BufferedState<P>
    where P: ToStatic,
{
    type Static = BufferedState<P::Static>;
    fn to_static(self) -> Self::Static {
        BufferedState(self.0.to_static(), self.1)
    }
}
    
impl<'a, P> InferOutput<Chars<'a>> for BufferedState<P>
{
    type Output = Cow<'a, str>;
}

impl<'a, P> Stateful<Chars<'a>, Cow<'a, str>> for BufferedState<P>
    where P: StatefulInfer<Chars<'a>>
{

    fn more(mut self, data: &mut Chars<'a>) -> ParseResult<Self, Cow<'a, str>> {
        let string = data.as_str();
        match self.0.more(data) {
            Done(_) => {
                self.1.push_str(&string[..(string.len() - data.as_str().len())]);
                Done(Owned(self.1))
            },
            Continue(state) => {
                self.1.push_str(string);
                Continue(BufferedState(state, self.1))
            },
        }
    }

    fn done(self) -> Cow<'a, str> {
        Owned(self.1)
    }

}

// ----------- Parsers which are boxable -------------

#[derive(Debug)]
pub struct BoxableState<P>(Option<P>);

impl<P1, P2> Upcast<BoxableState<P2>> for BoxableState<P1>
    where P1: Upcast<P2>,
{
    fn upcast(self) -> BoxableState<P2> {
        BoxableState(self.0.upcast())
    }
}

impl<P> ToStatic for BoxableState<P>
    where P: ToStatic,
{
    type Static = BoxableState<P::Static>;
    fn to_static(self) -> Self::Static {
        BoxableState(self.0.to_static())
    }
}

impl<P, Input> InferOutput<Input> for BoxableState<P>
    where P: InferOutput<Input>,
{
    type Output = P::Output;
}

impl<P, Input, Output> Boxable<Input, Output> for BoxableState<P>
    where P: Stateful<Input, Output>,
{
    fn more_boxable(&mut self, data: &mut Input) -> ParseResult<(), Output> {
        match self.0.take().unwrap().more(data) {
            Done(result) => Done(result),
            Continue(state) => {
                self.0 = Some(state);
                Continue(())
            }
        }
    }
    fn done_boxable(&mut self) -> Output {
        self.0.take().unwrap().done()
    }
}

impl<P, Input> InferOutput<Input> for Box<P>
    where P: InferOutput<Input>,
{
    type Output = P::Output;
}

impl<P: ?Sized, Input, Output> Stateful<Input, Output> for Box<P>
    where P: Boxable<Input, Output>,
{
    fn more(mut self, data: &mut Input) -> ParseResult<Self, Output> {
        match self.more_boxable(data) {
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

#[derive(Debug, Copy, Clone)]
pub struct Boxed<P, F>(P, F);

impl<P, F> Parser for Boxed<P, F> where P: Parser {}

impl<P, F, Input> InferOutput<Input> for Boxed<P, F>
    where P: InferOutput<Input>,
{
    type Output = P::Output;
}

impl<P, F, Input, Output> Uncommitted<Input, Output> for Boxed<P, F>
    where P: Uncommitted<Input, Output>,
          F: Function<BoxableState<P::State>>,
          F::Output: Stateful<Input, Output>,
{
    type State = F::Output;

    fn init(&self, data: &mut Input) -> Option<ParseResult<F::Output, Output>> {
        match self.0.init(data) {
            None => None,
            Some(Done(result)) => Some(Done(result)),
            Some(Continue(parsing)) => Some(Continue(self.1.apply(BoxableState::new(parsing)))),
        }
    }
}

impl<P, F, Input, Output> Committed<Input, Output> for Boxed<P, F>
    where P: Committed<Input, Output>,
          F: Function<BoxableState<P::State>>,
          F::Output: Stateful<Input, Output>,
{
    fn empty(&self) -> Output {
        self.0.empty()
    }
}

impl<P, F> Boxed<P, F> {
    pub fn new(parser: P, function: F) -> Self {
        Boxed(parser, function)
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

// // TODO: restore these

// // #[derive(Copy, Clone, Debug)]
// // pub struct PipeStateful<P, Q, R>(P, Q, R);

// // impl<P, Q, Str> Stateful<Str> for PipeStateful<P, P::State, Q>
// //     where P: Copy + Committed<Str>,
// //           Q: Stateful<Peekable<IterParser<P, P::State, Str>>>,
// //           Str: IntoPeekable,
// //           Str::Item: ToStatic,
// //           P::State: Stateful<Str>,
// // {
// //     type Output = Q::Output;
// //     fn parse(self, data: Str) -> ParseResult<Self, Str> {
// //         let iterator = Peekable::new(IterParser(self.0, Some((self.1, data))));
// //         match self.2.parse(iterator) {
// //             Done(rest, result) => Done(rest.iter.1.unwrap().1, result),
// //             Continue(rest, parsing2) => {
// //                 let (parsing1, data) = rest.iter.1.unwrap();
// //                 Continue(data, PipeStateful(self.0, parsing1, parsing2))
// //             }
// //         }
// //     }
// //     fn done(self) -> Q::Output {
// //         // TODO: feed the output of self.1.done() into self.2.
// //         self.1.done();
// //         self.2.done()
// //     }
// // }

// // #[derive(Copy, Clone, Debug)]
// // pub struct PipeParser<P, Q>(P, Q);

// // impl<P, Q, Ch> Parser<Ch> for PipeParser<P, Q>
// //     where P: 'static + Parser<Ch>,
// //           Q: Parser<Ch>,
// // {
// //     type State = PipeStateful<P,P::State,Q::State>;
// //     type StaticOutput = Q::StaticOutput;
// // }

// // impl<P, Q, Str> Committed<Str> for PipeParser<P, Q>
// //     where P: 'static + Copy + Committed<Str>,
// //           Q: for<'a> Committed<Peekable<&'a mut IterParser<P, P::State, Str>>>,
// //           Str: IntoPeekable,
// //           Str::Item: ToStatic,
// //           P::State: Stateful<Str>,
// // {
// //     fn init(&self) -> Self::State {
// //         PipeStateful(self.0, self.0.init(), self.1.init())
// //     }
// // }

// // impl<P, Q> PipeParser<P, Q> {
// //     pub fn new(lhs: P, rhs: Q) -> Self {
// //         PipeParser(lhs, rhs)
// //     }
// // }

