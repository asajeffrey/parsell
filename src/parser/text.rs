use parser::combinators::{Parser, ParseTo, Consumer, ErrConsumer, token, token_match};
use parser::lexer::{Token};
use parser::lexer::Token::{Begin, End, Identifier, Number};

use ast::{Memory, Module, Typ, Var};
use ast::Typ::{F32, F64, I32, I64};

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum ParseError {
    ExpectingTyp(String),
    ExpectingId(String),
    ExpectingNumber(String),
}

pub trait ParserConsumer<D> where D: Consumer<Module>+ErrConsumer<ParseError> {
    fn accept<P>(self, parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],D>;
}

fn is_identifier<'a>(tok: Token<'a>) -> bool {
    match tok {
        Identifier(_) => true,
        _             => false,
    }
}

fn is_number<'a>(tok: Token<'a>) -> bool {
    match tok {
        Number(_) => true,
        _         => false,
    }
}

fn is_begin_memory<'a>(tok: Token<'a>) -> bool { tok == Begin("memory") }
fn is_begin_module<'a>(tok: Token<'a>) -> bool { tok == Begin("module") }
fn is_begin_param<'a>(tok: Token<'a>) -> bool { tok == Begin("param") }
fn is_end<'a>(tok: Token<'a>) -> bool { tok == End }

fn mk_usize<'a>(tok: Token<'a>) -> Result<usize,ParseError> {
    match tok {
        Number(n) => Ok(n),
        _         => Err(ParseError::ExpectingNumber(String::from(tok))),
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

fn mk_var(children: (String,Typ)) -> Var {
    Var{ name: children.0, typ: children.1 }
}

fn mk_memory<'a>(children: (usize, Option<usize>)) -> Memory {
    Memory{ init: children.0, max: children.1, segments: vec![] }
}

fn mk_module<'a>(children: Option<Memory>) -> Module {
    Module{ memory: children, imports: vec![], exports: vec![], functions: vec![] }
}

pub fn parser<C,D>(consumer: C) where C: ParserConsumer<D>, D: Consumer<Module>+ErrConsumer<ParseError> {
    let typ = token_match(is_identifier)
        .map(mk_typ).results();
    let id = token_match(is_identifier)
        .map(mk_id).results();
    let number = token_match(is_number)
        .map(mk_usize).results();
    let memory = token_match(is_begin_memory).ignore()
        .and_then(number)
        .zip(number.map(Some).or_emit(None))
        .and_then(token_match(is_end).ignore())
        .map(mk_memory);
    let module = token_match(is_begin_module).ignore()
        .and_then(memory.map(Some).or_emit(None))
        .and_then(token_match(is_end).ignore())
        .map(mk_module);
    let top_level = module;
    consumer.accept(top_level);
}

#[test]
fn test_parser() {
    use parser::combinators::MatchResult::{Matched,Failed};
    struct TestConsumer(Vec<Module>,Vec<ParseError>);
    impl Consumer<Module> for TestConsumer {
        fn accept(&mut self, module: Module) {
            self.0.push(module);
        }
    }
    impl ErrConsumer<ParseError> for TestConsumer {
        fn error(&mut self, err: ParseError) {
            self.1.push(err);
        }
    }
    impl ParserConsumer<TestConsumer> for TestConsumer {
        fn accept<P>(mut self, mut parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],TestConsumer> {
            let tokens = [
                Begin("module"),
                    Begin("memory"),
                        Number(1024),
                    End,
                End,
            ];
            let ast = Module{
                memory: Some(Memory{
                    init: 1024,
                    max: None,
                    segments: vec![],
                }),
                imports: vec![],
                exports: vec![],
                functions: vec![]
            };
            assert_eq!(parser.done_to(&mut self), false);
            assert_eq!(self.0, []);
            assert_eq!(self.1, []);
            assert_eq!(parser.push_to(&tokens, &mut self), Matched(None));
            assert_eq!(parser.done_to(&mut self), true);
            assert_eq!(self.0, [ast]);
            assert_eq!(self.1, []);
        }
    }
    parser(TestConsumer(Vec::new(),Vec::new()));
}
