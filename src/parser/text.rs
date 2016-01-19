use parser::combinators::{Parser, ParseTo, Consumer, token, tokens};
use parser::lexer::{Token};
use parser::lexer::Token::{Identifier};
use ast::{Typ, Var};
use ast::Typ::{F32, F64, I32, I64};

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum ParseError {
    ExpectingTyp(String),
    ExpectingId(String),
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

fn is_param<'a>(tok: Token<'a>) -> bool {
    match tok {
        Identifier("param") => true,
        _                   => false,
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

fn mk_id<'a>(tok: Token<'a>) -> Result<String,ParseError> {
    match tok {
        Identifier(x) => Ok(String::from(x)),
        _             => Err(ParseError::ExpectingId(String::from(tok))),
    }
}

fn mk_var<'a>(children: (Result<String,ParseError>, Result<Typ,ParseError>))-> Result<Var,ParseError> {
    Ok(Var { name: try!(children.0), typ: try!(children.1) })
}

pub fn var_parser<C,D>(consumer: C) where C: ParserConsumer<Var,D>, D: Consumer<Result<Var,ParseError>> {
    let typ = token(is_identifier).map(mk_typ);
    let id = token(is_identifier).map(mk_id);
    let param = token(is_param).ignore().and_then(id).zip(typ).map(mk_var);
    consumer.accept(param);
}

#[test]
fn test_var() {
    use parser::combinators::MatchResult::{Matched,Failed};
    use parser::lexer::Token::{LParen};
    struct TestConsumer;
    impl ParserConsumer<Var,Vec<Result<Var,ParseError>>> for TestConsumer {
        fn accept<P>(self, mut parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],Vec<Result<Var,ParseError>>> {
            let mut results = Vec::new();
            assert_eq!(parser.done_to(&mut results), false);
            assert_eq!(results, []);
            results.clear();
            assert_eq!(parser.push_to(&[Identifier("param"),Identifier("$x"),Identifier("f32")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Ok(Var{ name: String::from("$x"), typ: F32 })]);
            results.clear();
            assert_eq!(parser.push_to(&[LParen], &mut results), Failed(Some(&[LParen][..])));
            assert_eq!(parser.done_to(&mut results), false);
            assert_eq!(results, []);
            results.clear();
            assert_eq!(parser.push_to(&[Identifier("param"),Identifier("$x"),Identifier("foo")], &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Err(ParseError::ExpectingTyp(String::from("foo")))]);
            results.clear();
        }
    }
    var_parser(TestConsumer);
}
