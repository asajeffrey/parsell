//! Provide implementations of parser traits.

// use super::{Stateful, Parser, Uncommitted, Committed, Boxable, ParseResult, MaybeParseResult,
//             Factory, Function, Consumer, ToStatic, Peekable, IntoPeekable};
// use super::ParseResult::{Continue, Done};
// use super::MaybeParseResult::{Abort, Commit, Empty};

use super::{Parser};
use super::{Stateful, StatefulOutput, StatefulParseChStrResult};
use super::{Committed, CommittedOutput, CommittedParseChStrResult};
use super::{Uncommitted, UncommittedOutput, UncommittedParseChStrResult};
use super::{Function};
use super::{Impossible};
use super::{ToStatic, Static};
use super::Maybe::{Empty, Backtrack, Commit};
use super::ParseResult::{Done, Continue};

// // use self::OrElseStatefulParser::{Lhs, Rhs};
// use self::OrElseCommittedParser::{Uncommit, CommitLhs, CommitRhs};
use self::AndThenState::{InLhs, InRhs};

// use std::borrow::Cow;
// use std::borrow::Cow::{Borrowed, Owned};
// use std::str::Chars;
use std::fmt::{Formatter, Debug};
use std;


// // ----------- N-argument functions ---------------

// #[derive(Copy, Clone, Debug)]
// pub struct Function2<F>(F);

// impl<F> Function2<F> {
//     pub fn new(f: F) -> Self {
//         Function2(f)
//     }
// }

// // NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// // See https://github.com/rust-lang/rust/issues/30867 for more details.
// impl<F, S1, S2> Function<(S1, S2)> for Function2<F> where F: Fn<(S1, S2, )>
// {
//     type Output = F::Output;
//     fn apply(&self, args: (S1, S2)) -> F::Output {
//         (self.0)(args.0, args.1)
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct Function3<F>(F);

// impl<F> Function3<F> {
//     pub fn new(f: F) -> Self {
//         Function3(f)
//     }
// }

// // NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// // See https://github.com/rust-lang/rust/issues/30867 for more details.
// impl<F, S1, S2, S3> Function<((S1, S2), S3)> for Function3<F> where F: Fn<(S1, S2, S3, )>
// {
//     type Output = F::Output;
//     fn apply(&self, args: ((S1, S2), S3)) -> F::Output {
//         (self.0)((args.0).0, (args.0).1, args.1)
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct Function4<F>(F);

// impl<F> Function4<F> {
//     pub fn new(f: F) -> Self {
//         Function4(f)
//     }
// }

// // NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// // See https://github.com/rust-lang/rust/issues/30867 for more details.
// impl<F, S1, S2, S3, S4> Function<(((S1, S2), S3), S4)> for Function4<F>
//     where F: Fn<(S1, S2, S3, S4, )>
// {
//     type Output = F::Output;
//     fn apply(&self, args: (((S1, S2), S3), S4)) -> F::Output {
//         (self.0)(((args.0).0).0, ((args.0).0).1, (args.0).1, args.1)
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct Function5<F>(F);

// impl<F> Function5<F> {
//     pub fn new(f: F) -> Self {
//         Function5(f)
//     }
// }

// // NOTE(eddyb): a generic over U where F: Fn(T) -> U doesn't allow HRTB in both T and U.
// // See https://github.com/rust-lang/rust/issues/30867 for more details.
// impl<F, S1, S2, S3, S4, S5> Function<((((S1, S2), S3), S4), S5)> for Function5<F>
//     where F: Fn<(S1, S2, S3, S4, S5, )>
// {
//     type Output = F::Output;
//     fn apply(&self, args: ((((S1, S2), S3), S4), S5)) -> F::Output {
//         (self.0)((((args.0).0).0).0,
//                  (((args.0).0).0).1,
//                  ((args.0).0).1,
//                  (args.0).1,
//                  args.1)
//     }
// }

// // ----------- Deal with errors ---------------

// #[derive(Copy, Clone, Debug)]
// pub struct Try<F>(F);
// impl<F, S, E> Function<Result<S, E>> for Try<F> where F: Function<S>
// {
//     type Output = Result<F::Output,E>;
//     fn apply(&self, args: Result<S, E>) -> Result<F::Output, E> {
//         Ok(self.0.apply(try!(args)))
//     }
// }
// impl<F> Try<F> {
//     pub fn new(f: F) -> Try<F> {
//         Try(f)
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct TryZip;
// impl<S, T, E> Function<(Result<S, E>, T)> for TryZip {
//     type Output = Result<(S,T),E>;
//     fn apply(&self, args: (Result<S, E>, T)) -> Result<(S, T), E> {
//         Ok((try!(args.0), args.1))
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct ZipTry;
// impl<S, T, E> Function<(S, Result<T, E>)> for ZipTry {
//     type Output = Result<(S,T),E>;
//     fn apply(&self, args: (S, Result<T, E>)) -> Result<(S, T), E> {
//         Ok((args.0, try!(args.1)))
//     }
// }

// #[derive(Copy, Clone, Debug)]
// pub struct TryZipTry;
// impl<S, T, E> Function<(Result<S, E>, Result<T, E>)> for TryZipTry {
//     type Output = Result<(S,T),E>;
//     fn apply(&self, args: (Result<S, E>, Result<T, E>)) -> Result<(S, T), E> {
//         Ok((try!(args.0), try!(args.1)))
//     }
// }

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

impl<P, F, Str> Stateful<Str> for Map<P, F>
    where P: Stateful<Str>,
          F: Function<StatefulOutput<P, Str>>,
          Str: Iterator,
{
    
    type Output = F::Output;

    fn more_eof(self) -> StatefulOutput<Self, Str> {
        self.1.apply(self.0.more_eof())
    }

    fn more_ch_str(self, ch: Str::Item, string: Str) -> StatefulParseChStrResult<Self, Str>  {
        match self.0.more_ch_str(ch, string) {
            Done((ch, string, result)) => Done((ch, string, self.1.apply(result))),
            Continue((empty, parsing)) => Continue((empty, Map(parsing, self.1))),
        }
    }

}

impl<P, F, Str> Committed<Str> for Map<P, F>
    where P: Committed<Str>,
          F: Copy + Function<CommittedOutput<P, Str>>,
          Str: Iterator,
{

    type State = Map<P::State, F>;
    
    fn init_ch_str(&self, ch: Str::Item, string: Str) -> CommittedParseChStrResult<Self, Str> {
        match self.0.init_ch_str(ch, string) {
            Done((ch, string, result)) => Done((ch, string, self.1.apply(result))),
            Continue((empty, parsing)) => Continue((empty, Map(parsing, self.1))),
        }
    }

    fn init_eof(&self) -> CommittedOutput<Self, Str> {
        self.1.apply(self.0.init_eof())
    }

}

impl<P, F, Str> Uncommitted<Str> for Map<P, F>
    where P: Uncommitted<Str>,
          F: Copy + Function<UncommittedOutput<P, Str>>,
          Str: Iterator,
{

    type State = Map<P::State, F>;
    
    fn init_ch_str(&self, ch: Str::Item, string: Str) -> UncommittedParseChStrResult<Self, Str> {
        match self.0.init_ch_str(ch, string) {
            Empty(impossible) => Empty(impossible),
            Backtrack((ch, string)) => Backtrack((ch, string)),
            Commit(Done((ch, string, result))) => Commit(Done((ch, string, self.1.apply(result)))),
            Commit(Continue((empty, parsing))) => Commit(Continue((empty, Map(parsing, self.1)))),
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

impl<P, Q, Str> Committed<Str> for AndThen<P, Q>
    where P: Committed<Str>,
          Q: Copy+Committed<Str>,
          Str: Iterator,
          CommittedOutput<P, Str>: ToStatic,
{
    
    type State = AndThenState<(P::State, Q), (Static<CommittedOutput<P, Str>>, Q::State)>;

    fn init_ch_str(&self, ch: Str::Item, string: Str) -> CommittedParseChStrResult<Self, Str> {
        match self.0.init_ch_str(ch, string) {
            Done((ch, string, fst)) => match self.1.init_ch_str(ch, string) {
                Done((ch, string, snd)) => Done((ch, string, (fst, snd))),
                Continue((empty, snd)) => Continue((empty, InRhs((fst.to_static(), snd)))),
            },
            Continue((empty, fst)) => Continue((empty, InLhs((fst, self.1)))),
        }
    }
    
    fn init_eof(&self) -> CommittedOutput<Self, Str> {
        (self.0.init_eof(), self.1.init_eof())
    }

}

impl<P, Q, Str> Uncommitted<Str> for AndThen<P, Q>
    where P: Uncommitted<Str>,
          Q: Copy+Committed<Str>,
          Str: Iterator,
          UncommittedOutput<P, Str>: ToStatic,
{
    
    type State = AndThenState<(P::State, Q), (Static<UncommittedOutput<P, Str>>, Q::State)>;

    fn init_ch_str(&self, ch: Str::Item, string: Str) -> UncommittedParseChStrResult<Self, Str> {
        match self.0.init_ch_str(ch, string) {
            Empty(impossible) => Empty(impossible),
            Backtrack((ch, string)) => Backtrack((ch, string)),
            Commit(Done((ch, string, fst))) => match self.1.init_ch_str(ch, string) {
                Done((ch, string, snd)) => Commit(Done((ch, string, (fst, snd)))),
                Continue((empty, snd)) => Commit(Continue((empty, InRhs((fst.to_static(), snd))))),
            },
            Commit(Continue((empty, fst))) => Commit(Continue((empty, InLhs((fst, self.1))))),
        }
    }

}

impl<P, Q> AndThen<P, Q> {
    pub fn new(p: P, q: Q) -> Self {
        AndThen(p, q)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum AndThenState<P, Q> {
    InLhs(P),
    InRhs(Q),
}

impl<P, Q, Str> Stateful<Str> for AndThenState<(P, Q), (Static<StatefulOutput<P, Str>>, Q::State)>
    where P: Stateful<Str>,
          Q: Committed<Str>,
          Str: Iterator,
          StatefulOutput<P, Str>: ToStatic,
{
    
    type Output = (StatefulOutput<P, Str>, CommittedOutput<Q, Str>);

    fn more_eof(self) -> StatefulOutput<Self, Str>
    {
        match self {
            InLhs((fst, snd)) => (fst.more_eof(), snd.init_eof()),
            InRhs((fst, snd)) => (ToStatic::from_static(fst), snd.more_eof()),
        }
    }

    fn more_ch_str(self, ch: Str::Item, string: Str) -> StatefulParseChStrResult<Self, Str>
    {
        match self {
            InLhs((fst, snd)) => {
                match fst.more_ch_str(ch, string) {
                    Done((ch, string, fst)) => match snd.init_ch_str(ch, string) {
                        Done((ch, string, snd)) => Done((ch, string, (fst, snd))),
                        Continue((string, snd)) => Continue((string, InRhs((fst.to_static(), snd)))),
                    },
                    Continue((string, fst)) => Continue((string, InLhs((fst, snd)))),
                }
            }
            InRhs((fst, snd)) => {
                match snd.more_ch_str(ch, string) {
                    Done((ch, string, snd)) => Done((ch, string, (ToStatic::from_static(fst), snd))),
                    Continue((string, snd)) => Continue((string, InRhs((fst, snd)))),
                }
            }
        }
    }
   
}

// impl<P, Q> AndThenParser<P, Q> {
//     pub fn new(lhs: P, rhs: Q) -> Self {
//         AndThenParser(lhs, rhs)
//     }
// }

// // ----------- Choice ---------------

// #[derive(Copy, Clone, Debug)]
// pub struct OrElseParser<P, Q>(P, Q);

// impl<P, Q, Ch> Parser<Ch> for OrElseParser<P, Q>
//     where P: 'static + Parser<Ch>,
//           Q: Parser<Ch>,
// {
//     type StaticOutput = P::StaticOutput;
//     type State = OrElseCommittedParser<P,P::State,Q::State>;
// }
// impl<P, Q, Str> Committed<Str> for OrElseParser<P, Q>
//     where P: 'static + Copy + Uncommitted<Str>,
//           Q: Committed<Str>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
// {
//     fn init(&self) -> Self::State {
//         Uncommit(self.0, self.1.init())
//     }
// }
// impl<P, Q, Str> Uncommitted<Str> for OrElseParser<P, Q>
//     where P: 'static + Uncommitted<Str>,
//           Q: Uncommitted<Str>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
//           Q::State: Stateful<Str, Output = <P::State as Stateful<Str>>::Output>,
// {
//     fn parse(&self, value: Str) -> MaybeParseResult<Self::State, Str> {
//         match self.0.parse(value) {
//             Empty(rest) => Empty(rest),
//             Commit(Done(rest, result)) => Commit(Done(rest, result)),
//             Commit(Continue(rest, parsing)) => Commit(Continue(rest, CommitLhs(parsing))),
//             Abort(value) => {
//                 match self.1.parse(value) {
//                     Empty(rest) => Empty(rest),
//                     Commit(Done(rest, result)) => Commit(Done(rest, result)),
//                     Commit(Continue(rest, parsing)) => Commit(Continue(rest, CommitRhs(parsing))),
//                     Abort(value) => Abort(value),
//                 }
//             }
//         }
//     }
// }

// impl<P, Q> OrElseParser<P, Q> {
//     pub fn new(lhs: P, rhs: Q) -> Self {
//         OrElseParser(lhs, rhs)
//     }
// }

// // #[derive(Copy, Clone, Debug)]
// // pub enum OrElseStatefulParser<P, Q> {
// //     Lhs(P),
// //     Rhs(Q),
// // }

// // impl<P, Q, Str> Stateful<Str> for OrElseStatefulParser<P, Q>
// //     where P: Stateful<Str>,
// //           Q: Stateful<Str, Output = P::Output>
// // {
// //     type Output = P::Output;
// //     fn parse(self, value: Str) -> ParseResult<Self, Str> {
// //         match self {
// //             Lhs(lhs) => {
// //                 match lhs.parse(value) {
// //                     Done(rest, result) => Done(rest, result),
// //                     Continue(rest, parsing) => Continue(rest, Lhs(parsing)),
// //                 }
// //             }
// //             Rhs(rhs) => {
// //                 match rhs.parse(value) {
// //                     Done(rest, result) => Done(rest, result),
// //                     Continue(rest, parsing) => Continue(rest, Rhs(parsing)),
// //                 }
// //             }
// //         }
// //     }
// //     fn done(self) -> Self::Output {
// //         match self {
// //             Lhs(lhs) => lhs.done(),
// //             Rhs(rhs) => rhs.done(),
// //         }
// //     }
// // }

// #[derive(Copy, Clone, Debug)]
// pub enum OrElseCommittedParser<P, Q, R> {
//     Uncommit(P, R),
//     CommitLhs(Q),
//     CommitRhs(R),
// }

// impl<P, Q, Str> Stateful<Str> for OrElseCommittedParser<P, P::State, Q>
//     where P: Uncommitted<Str>,
//           Q: Stateful<Str>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str, Output = Q::Output>,
// {
//     type Output = Q::Output;
//     fn parse(self, value: Str) -> ParseResult<Self, Str> {
//         match self {
//             Uncommit(lhs, rhs) => {
//                 match lhs.parse(value) {
//                     Empty(value) => Continue(value, Uncommit(lhs, rhs)),
//                     Commit(Done(rest, result)) => Done(rest, result),
//                     Commit(Continue(rest, parsing)) => Continue(rest, CommitLhs(parsing)),
//                     Abort(value) => {
//                         match rhs.parse(value) {
//                             Done(rest, result) => Done(rest, result),
//                             Continue(rest, parsing) => Continue(rest, CommitRhs(parsing)),
//                         }
//                     }
//                 }
//             }
//             CommitLhs(lhs) => {
//                 match lhs.parse(value) {
//                     Done(rest, result) => Done(rest, result),
//                     Continue(rest, parsing) => Continue(rest, CommitLhs(parsing)),
//                 }
//             }
//             CommitRhs(rhs) => {
//                 match rhs.parse(value) {
//                     Done(rest, result) => Done(rest, result),
//                     Continue(rest, parsing) => Continue(rest, CommitRhs(parsing)),
//                 }
//             }
//         }
//     }
//     fn done(self) -> Self::Output {
//         match self {
//             Uncommit(_, rhs) => rhs.done(),
//             CommitLhs(lhs) => lhs.done(),
//             CommitRhs(rhs) => rhs.done(),
//         }
//     }
// }

// // ----------- Kleene star ---------------

// #[derive(Clone,Debug)]
// pub struct StarStatefulParser<P, Q, T>(P, Option<Q>, T);

// impl<P, T, Str> Stateful<Str> for StarStatefulParser<P, P::State, T>
//     where P: Copy + Uncommitted<Str>,
//           T: Consumer<<P::State as Stateful<Str>>::Output>,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
// {
//     type Output = T;
//     fn parse(mut self, mut value: Str) -> ParseResult<Self, Str> {
//         loop {
//             match self.1.take() {
//                 None => {
//                     match self.0.parse(value) {
//                         Empty(rest) => {
//                             return Continue(rest, StarStatefulParser(self.0, None, self.2))
//                         }
//                         Commit(Continue(rest, parsing)) => {
//                             return Continue(rest,
//                                             StarStatefulParser(self.0, Some(parsing), self.2))
//                         }
//                         Commit(Done(rest, result)) => {
//                             self.2.accept(result);
//                             value = rest;
//                         }
//                         Abort(rest) => return Done(rest, self.2),
//                     }
//                 }
//                 Some(parser) => {
//                     match parser.parse(value) {
//                         Continue(rest, parsing) => {
//                             return Continue(rest,
//                                             StarStatefulParser(self.0, Some(parsing), self.2))
//                         }
//                         Done(rest, result) => {
//                             self.2.accept(result);
//                             value = rest;
//                         }
//                     }
//                 }
//             }
//         }
//     }
//     fn done(self) -> T {
//         self.2
//     }
// }

// pub struct PlusParser<P, F>(P, F);

// // A work around for functions implmenting copy but not clone
// // https://github.com/rust-lang/rust/issues/28229
// impl<P, F> Copy for PlusParser<P, F>
//     where P: Copy,
//           F: Copy
// {}
// impl<P, F> Clone for PlusParser<P, F>
//     where P: Clone,
//           F: Copy
// {
//     fn clone(&self) -> Self {
//         PlusParser(self.0.clone(), self.1)
//     }
// }

// // A work around for named functions not implmenting Debug
// // https://github.com/rust-lang/rust/issues/31522
// impl<P, F> Debug for PlusParser<P, F>
//     where P: Debug
// {
//     fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
//         write!(fmt, "PlusParser({:?}, ...)", self.0)
//     }
// }

// impl<P, F, Ch> Parser<Ch> for PlusParser<P, F>
//     where P: 'static + Parser<Ch>,
//           F: Factory,
//           F::Output: 'static,
// {
//     type State = StarStatefulParser<P,P::State,F::Output>;
//     type StaticOutput = F::Output;
// }
// impl<P, F, Str> Uncommitted<Str> for PlusParser<P, F>
//     where P: 'static + Copy + Uncommitted<Str>,
//           F: 'static + Factory,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
//           F::Output: Consumer<<P::State as Stateful<Str>>::Output>,
// {
//     fn parse(&self, value: Str) -> MaybeParseResult<Self::State, Str> {
//         match self.0.parse(value) {
//             Empty(rest) => Empty(rest),
//             Abort(rest) => Abort(rest),
//             Commit(Continue(rest, parsing)) => {
//                 Commit(Continue(rest,
//                                 StarStatefulParser(self.0, Some(parsing), self.1.build())))
//             }
//             Commit(Done(rest, result)) => {
//                 let mut buffer = self.1.build();
//                 buffer.accept(result);
//                 Commit(StarStatefulParser(self.0, None, buffer).parse(rest))
//             }
//         }
//     }
// }

// impl<P, F> PlusParser<P, F> {
//     pub fn new(parser: P, factory: F) -> Self {
//         PlusParser(parser, factory)
//     }
// }

// pub struct StarParser<P, F>(P, F);

// // A work around for functions implmenting copy but not clone
// // https://github.com/rust-lang/rust/issues/28229
// impl<P, F> Copy for StarParser<P, F>
//     where P: Copy,
//           F: Copy
// {}
// impl<P, F> Clone for StarParser<P, F>
//     where P: Clone,
//           F: Copy
// {
//     fn clone(&self) -> Self {
//         StarParser(self.0.clone(), self.1)
//     }
// }

// // A work around for named functions not implmenting Debug
// // https://github.com/rust-lang/rust/issues/31522
// impl<P, F> Debug for StarParser<P, F>
//     where P: Debug
// {
//     fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
//         write!(fmt, "StarParser({:?}, ...)", self.0)
//     }
// }

// impl<P, F, Ch> Parser<Ch> for StarParser<P, F>
//     where P: 'static + Parser<Ch>,
//           F: 'static + Factory,
// {
//     type StaticOutput = F::Output;
//     type State = StarStatefulParser<P,P::State,F::Output>;
// }
// impl<P, F, Str> Committed<Str> for StarParser<P, F>
//     where P: 'static + Copy + Uncommitted<Str>,
//           F: 'static + Factory,
//           Str: IntoPeekable,
//           Str::Item: ToStatic,
//           P::State: Stateful<Str>,
//           F::Output: Consumer<<P::State as Stateful<Str>>::Output>
// {
//     fn init(&self) -> Self::State {
//         StarStatefulParser(self.0, None, self.1.build())
//     }
// }

// impl<P, F> StarParser<P, F> {
//     pub fn new(parser: P, factory: F) -> Self {
//         StarParser(parser, factory)
//     }
// }

// ----------- A type for parsers which don't exist -------------

impl<Str> Stateful<Str> for Impossible where Str: Iterator {

    type Output = Str::Item;
    
    fn more_ch_str(self, _: Str::Item, _: Str) -> StatefulParseChStrResult<Self, Str> {
        self.cant_happen()
    }
    
    fn more_eof(self) -> Str::Item {
        self.cant_happen()
    }
    
}

// ----------- A type for parsers which immediately return -------------

#[derive(Copy, Clone, Debug)]
pub struct Return<T>(T);

impl<T> Parser for Return<T> {}

impl<T, Str> Stateful<Str> for Return<T> where Str: Iterator {

    type Output = T;
    
    fn more_ch_str(self, ch: Str::Item, string: Str) -> StatefulParseChStrResult<Self, Str> {
        Done((ch, string, self.0))
    }
    
    fn more_eof(self) -> T {
        self.0
    }
    
}

impl<T, Str> Committed<Str> for Return<T> where Str: Iterator, T: Copy {

    type State = Self;

    fn init_ch_str(&self, ch: Str::Item, string: Str) -> CommittedParseChStrResult<Self, Str> {
        Done((ch, string, self.0))
    }
    
    fn init_eof(&self) -> T {
        self.0
    }
    
}

impl<T> Return<T> {
    pub fn new(t: T) -> Self {
        Return(t)
    }
}

// ----------- Character parsers -------------

pub struct Character<F>(F);

// A work around for functions implmenting copy but not clone
// https://github.com/rust-lang/rust/issues/28229
impl<F> Copy for Character<F> where F: Copy
{}
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

impl<F, Str> Uncommitted<Str> for Character<F>
    where Str: Iterator,
          F: Function<Str::Item, Output = bool>,
          Str::Item: Copy,
{
    
    type State = Return<Str::Item>;
    
    fn init_ch_str(&self, ch: Str::Item, string: Str) -> UncommittedParseChStrResult<Self, Str> {
        if self.0.apply(ch) {
            Commit(Return(ch).more_str(string))
        } else {
            Backtrack((ch, string))
        }
    }
    
}

impl<F> Character<F> {
    pub fn new(function: F) -> Self {
        Character(function)
    }
}

#[derive(Copy,Clone,Debug)]
pub struct AnyCharacter;

impl Parser for AnyCharacter {}

impl<Str> Committed<Str> for AnyCharacter
    where Str: Iterator,
{
    
    type State = Return<Option<Str::Item>>;
    
    fn init_ch_str(&self, ch: Str::Item, string: Str) -> CommittedParseChStrResult<Self, Str> {
        Return(Some(ch)).more_str(string)
    }

    fn init_eof(&self) -> Option<Str::Item> {
        None
    }
    
}

// // ----------- Token parsers -------------

// pub struct TokenParser<F>(F);

// // A work around for functions implmenting copy but not clone
// // https://github.com/rust-lang/rust/issues/28229
// impl<F> Copy for TokenParser<F> where F: Copy
// {}
// impl<F> Clone for TokenParser<F> where F: Copy
// {
//     fn clone(&self) -> Self {
//         TokenParser(self.0)
//     }
// }

// // A work around for named functions not implmenting Debug
// // https://github.com/rust-lang/rust/issues/31522
// impl<F> Debug for TokenParser<F>
// {
//     fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
//         write!(fmt, "TokenParser(...)")
//     }
// }

// impl<F, Ch> Parser<Ch> for TokenParser<F> where Ch: 'static
// {
//     type StaticOutput = Ch;
//     type State = Impossible;
// }
// impl<F, Iter> Uncommitted<Peekable<Iter>> for TokenParser<F>
//     where F: for<'a> Function<&'a Iter::Item, Output = bool>,
//           Iter: Iterator,
//           Iter::Item: ToStatic,
// {
//     fn parse(&self, mut iterator: Peekable<Iter>) -> MaybeParseResult<Self::State, Peekable<Iter>> {
//         let matched = match iterator.peek() {
//             None => None,
//             Some(tok) => Some(self.0.apply(tok)),
//         };
//         match matched {
//             None => Empty(iterator),
//             Some(true) => {
//                 let tok = iterator.next().unwrap();
//                 Commit(Done(iterator, tok))
//             }
//             Some(false) => Abort(iterator),
//         }
//     }
// }

// impl<F> TokenParser<F> {
//     pub fn new(function: F) -> Self {
//         TokenParser(function)
//     }
// }

// #[derive(Copy,Clone,Debug)]
// pub struct AnyTokenParser;

// impl<Ch> Parser<Ch> for AnyTokenParser where Ch: 'static {
//     type StaticOutput = Option<Ch>;
//     type State = Self;
// }
// impl<Iter> Stateful<Peekable<Iter>> for AnyTokenParser
//     where Iter: Iterator,
//           Iter::Item: ToStatic,
// {
//     type Output = Option<Iter::Item>;
//     fn parse(self, mut iterator: Peekable<Iter>) -> ParseResult<Self, Peekable<Iter>> {
//         match iterator.next() {
//             None => Continue(iterator, AnyTokenParser),
//             Some(tok) => Done(iterator, Some(tok)),
//         }
//     }
//     fn done(self) -> Self::Output {
//         None
//     }
// }
// impl<Str> Committed<Str> for AnyTokenParser
//     where Str: IntoPeekable,
//           Str::Item: ToStatic,
// {
//     fn init(&self) -> Self {
//         AnyTokenParser
//     }
// }

// // ----------- Buffering -------------

// // If m is a Uncommitted<&'a str>, then
// // m.buffer() is a Uncommitted<&'a str> with Output Cow<'a,str>.
// // It does as little buffering as it can, but it does allocate as buffer for the case
// // where the boundary marker of the input is misaligned with that of the parser.
// // For example, m is matching string literals, and the input is '"abc' followed by 'def"'
// // we have to buffer up '"abc'.

// // TODO(ajeffrey): make this code generic.

// #[derive(Copy, Clone, Debug)]
// pub struct BufferedParser<P>(P);

// impl<P> Parser<char> for BufferedParser<P> where P: Parser<char> {
//     type StaticOutput = Cow<'static,str>;
//     type State = BufferedStatefulParser<P::State>;
// }
// impl<'a, P, Q> Uncommitted<&'a str> for BufferedParser<P>
//     where P: Parser<char> + Uncommitted<&'a str, State=Q>, // TODO: Figure out why Parser is required here
//           Q: 'static+Stateful<&'a str>,
// {
//     fn parse(&self, value: &'a str) -> MaybeParseResult<Self::State, &'a str> {
//         match self.0.parse(value) {
//             Empty(rest) => Empty(rest),
//             Commit(Done(rest, _)) => {
//                 Commit(Done(rest, Borrowed(&value[..(value.len() - rest.len())])))
//             }
//             Commit(Continue(rest, parsing)) => {
//                 Commit(Continue(rest, BufferedStatefulParser(parsing, String::from(value))))
//             }
//             Abort(value) => Abort(value),
//         }
//     }
// }
// impl<'a, P> Committed<&'a str> for BufferedParser<P> where P: Committed<&'a str>
// {
//     fn init(&self) -> Self::State {
//         BufferedStatefulParser(self.0.init(), String::new())
//     }
// }

// impl<P> BufferedParser<P> {
//     pub fn new(parser: P) -> Self {
//         BufferedParser(parser)
//     }
// }

// #[derive(Clone,Debug)]
// pub struct BufferedStatefulParser<P>(P, String);

// impl<'a, P> Stateful<&'a str> for BufferedStatefulParser<P> where P: Stateful<&'a str>
// {
//     type Output = Cow<'a,str>;
//     fn parse(mut self, value: &'a str) -> ParseResult<Self, &'a str> {
//         match self.0.parse(value) {
//             Done(rest, _) if self.1.is_empty() => {
//                 Done(rest, Borrowed(&value[..(value.len() - rest.len())]))
//             }
//             Done(rest, _) => {
//                 self.1.push_str(&value[..(value.len() - rest.len())]);
//                 Done(rest, Owned(self.1))
//             }
//             Continue(rest, parsing) => {
//                 self.1.push_str(value);
//                 Continue(rest, BufferedStatefulParser(parsing, self.1))
//             }
//         }
//     }
//     fn done(self) -> Self::Output {
//         Owned(self.1)
//     }
// }

// // ----------- Parsers which are boxable -------------

// #[derive(Debug)]
// pub struct BoxableParser<P>(Option<P>);
// impl<P, S> Boxable<S> for BoxableParser<P> where P: Stateful<S>
// {
//     type Output = P::Output;
//     fn parse_boxable(&mut self, value: S) -> (S, Option<Self::Output>) {
//         match self.0.take().unwrap().parse(value) {
//             Done(rest, result) => (rest, Some(result)),
//             Continue(rest, parsing) => {
//                 self.0 = Some(parsing);
//                 (rest, None)
//             }
//         }
//     }
//     fn done_boxable(&mut self) -> Self::Output {
//         self.0.take().unwrap().done()
//     }
// }

// impl<P: ?Sized, S> Stateful<S> for Box<P> where P: Boxable<S>
// {
//     type Output = P::Output;
//     fn parse(mut self, value: S) -> ParseResult<Self, S> {
//         match self.parse_boxable(value) {
//             (rest, Some(result)) => Done(rest, result),
//             (rest, None) => Continue(rest, self),
//         }
//     }
//     fn done(mut self) -> Self::Output {
//         self.done_boxable()
//     }
// }

// impl<P> BoxableParser<P> {
//     pub fn new(parser: P) -> Self {
//         BoxableParser(Some(parser))
//     }
// }

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

