use parser::combinators::{Parser, ParseTo, Consumer, token};
use parser::lexer::{Token};
use parser::lexer::Token::{Identifier};
use ast::{Typ};
use ast::Typ::{F32, F64, I32, I64};

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum ParseError {
    ExpectingTyp(String),
}

pub trait ParserConsumer<T,D> where D: Consumer<Result<T,ParseError>> {
    fn accept<P>(self, parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],D>;
}

fn is_identifier<'a>(tok: Token<'a>) -> bool {
    match tok {
        Identifier(_) => true,
        _             => false,
    }
}

fn mk_typ<'a>(tok: Token<'a>) -> Result<Typ,ParseError> {
    match tok {
        Identifier("f32") => Ok(F32),
        Identifier("f64") => Ok(F64),
        Identifier("i32") => Ok(I32),
        Identifier("i64") => Ok(I64),
        _                 => Err(ParseError::ExpectingTyp(String::from(tok))),
    }
}

pub fn typ_parser<C,D>(consumer: C) where C: ParserConsumer<Typ,D>, D: Consumer<Result<Typ,ParseError>> {
    consumer.accept(token(is_identifier).map(mk_typ));
}

#[test]
fn test_typ() {
    use parser::combinators::MatchResult::{Matched,Failed};
    use parser::lexer::Token::{LParen};
    struct TestConsumer;
    impl ParserConsumer<Typ,Vec<Result<Typ,ParseError>>> for TestConsumer {
        fn accept<P>(self, mut parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],Vec<Result<Typ,ParseError>>> {
            let mut results = Vec::new();
            assert_eq!(parser.push_to(&[Identifier("f32")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Ok(F32)]);
            results.clear();
            assert_eq!(parser.push_to(&[Identifier("f64")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Ok(F64)]);
            results.clear();
            assert_eq!(parser.push_to(&[Identifier("i32")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Ok(I32)]);
            results.clear();
            assert_eq!(parser.push_to(&[Identifier("i64")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Ok(I64)]);
            results.clear();
            assert_eq!(parser.push_to(&[LParen], &mut results), Failed(Some(&[LParen][..])));
            assert_eq!(parser.done_to(&mut results), false);
            assert_eq!(results, []);
            results.clear();
            assert_eq!(parser.push_to(&[Identifier("foo")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Err(ParseError::ExpectingTyp(String::from("foo")))]);
            results.clear();
        }
    }
    typ_parser(TestConsumer);
}
