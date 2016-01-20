use parser::combinators::{Parser, ParseTo, Consumer, token, tokens};
use parser::lexer::{Token};
use parser::lexer::Token::{Begin, End, Identifier, Number};

use ast::{Memory, Module, Typ, Var};
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

fn is_begin_memory<'a>(tok: Token<'a>) -> bool { tok == Begin("memory") }
fn is_begin_module<'a>(tok: Token<'a>) -> bool { tok == Begin("module") }
fn is_begin_param<'a>(tok: Token<'a>) -> bool { tok == Begin("param") }
fn is_end<'a>(tok: Token<'a>) -> bool { tok == End }

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

fn mk_var(children: (Result<String,ParseError>, Result<Typ,ParseError>))-> Result<Var,ParseError> {
    Ok(Var{ name: try!(children.0), typ: try!(children.1) })
}

fn mk_memory<'a>(children: Result<usize,ParseError>) -> Result<Memory,ParseError> {
    Ok(Memory{ init: try!(children), max: None, segments: vec![] })
}

fn mk_module<'a>(children: Token<'a>) -> Result<Module,ParseError> {
    Ok(Module{ memory: None, imports: vec![], exports: vec![], functions: vec![] })
}

pub fn parser<C,D>(consumer: C) where C: ParserConsumer<Module,D>, D: Consumer<Result<Module,ParseError>> {
    let typ = token(is_identifier).map(mk_typ);
    let id = token(is_identifier).map(mk_id);
    let param = token(is_begin_param).ignore().and_then(id).zip(typ).and_then(token(is_end).ignore()).map(mk_var);
    let module = token(is_begin_module).and_then(token(is_end).ignore()).map(mk_module);
    let top_level = module;
    consumer.accept(top_level);
}

#[test]
fn test_parser() {
    use parser::combinators::MatchResult::{Matched,Failed};
    struct TestConsumer;
    impl ParserConsumer<Module,Vec<Result<Module,ParseError>>> for TestConsumer {
        fn accept<P>(self, mut parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],Vec<Result<Module,ParseError>>> {
            let mut results = Vec::new();
            let tokens = [
                Begin("module"),                
                End,
            ];
            let ast = Module{
                memory: None,
                imports: vec![],
                exports: vec![],
                functions: vec![]
            };
            assert_eq!(parser.done_to(&mut results), false);
            assert_eq!(results, []);
            results.clear();
            assert_eq!(parser.push_to(&tokens, &mut results), Matched(None));
            assert_eq!(parser.done_to(&mut results), true);
            assert_eq!(results, [Ok(ast)]);
            results.clear();
        }
    }
    parser(TestConsumer);
}
