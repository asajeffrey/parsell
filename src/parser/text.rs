use parser::combinators::{Parser, ParseTo, Consumer, ErrConsumer, token_match};
use parser::lexer::{Token};
use parser::lexer::Token::{Begin, End, Identifier, Number, Text};

use ast::{Export, Function, Import, Memory, Module, Segment, Typ, Var};
use ast::Typ::{F32, F64, I32, I64};

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum ParseError {
    ExpectingTyp(String),
    ExpectingId(String),
    ExpectingString(String),
    ExpectingNumber(String),
}

pub trait ParserConsumer<D> where D: Consumer<Module>+ErrConsumer<ParseError> {
    fn accept<P>(self, parser: P) where P: for<'a> ParseTo<&'a[Token<'a>],D>;
}

#[derive(Clone, Debug)]
struct ModuleContents {
    imports: Vec<Import>,
    exports: Vec<Export>,
    functions: Vec<Function>,
}

impl ModuleContents {
    fn new() -> ModuleContents {
        ModuleContents { imports: Vec::new(), exports: Vec::new(), functions: Vec::new() }
    }
}

impl Consumer<Export> for ModuleContents {
    fn accept(&mut self, export: Export) {
        self.exports.push(export);
    }
}

impl Consumer<Function> for ModuleContents {
    fn accept(&mut self, export: Function) {
        self.functions.push(export);
    }
}

impl Consumer<Import> for ModuleContents {
    fn accept(&mut self, import: Import) {
        self.imports.push(import);
    }
}

impl Module {
    pub fn new() -> Module {
        Module{ memory: None, exports: Vec::new(), imports: Vec::new(), functions: Vec::new() }
    }
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

fn is_text<'a>(tok: Token<'a>) -> bool {
    match tok {
        Text(_) => true,
        _         => false,
    }
}

fn is_begin_export<'a>(tok: Token<'a>) -> bool { tok == Begin("export") }
fn is_begin_func<'a>(tok: Token<'a>) -> bool { tok == Begin("func") }
fn is_begin_import<'a>(tok: Token<'a>) -> bool { tok == Begin("import") }
fn is_begin_memory<'a>(tok: Token<'a>) -> bool { tok == Begin("memory") }
fn is_begin_local<'a>(tok: Token<'a>) -> bool { tok == Begin("local") }
fn is_begin_module<'a>(tok: Token<'a>) -> bool { tok == Begin("module") }
fn is_begin_param<'a>(tok: Token<'a>) -> bool { tok == Begin("param") }
fn is_begin_result<'a>(tok: Token<'a>) -> bool { tok == Begin("result") }
fn is_begin_segment<'a>(tok: Token<'a>) -> bool { tok == Begin("segment") }
fn is_end<'a>(tok: Token<'a>) -> bool { tok == End }

fn mk_usize<'a>(tok: Token<'a>) -> Result<usize,ParseError> {
    match tok {
        Number(n) => Ok(n),
        _         => Err(ParseError::ExpectingNumber(String::from(tok))),
    }
}

fn mk_string<'a>(tok: Token<'a>) -> Result<String,ParseError> {
    match tok {
        Text(s) => Ok(String::from(s)), // TODO: escape sequences
        _       => Err(ParseError::ExpectingString(String::from(tok))),
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

fn mk_function(children: (((String,Vec<Var>),Option<Typ>),Vec<Var>)) -> Function {
    Function{ name: ((children.0).0).0, params: ((children.0).0).1, result: (children.0).1, locals: children.1, body: Vec::new() }
}

fn mk_segment(children: (usize, String)) -> Segment {
    Segment{ addr: children.0, data: children.1 }
}

fn mk_memory(children: ((usize, Option<usize>), Vec<Segment>)) -> Memory {
    Memory{ init: (children.0).0, max: (children.0).1, segments: children.1 }
}

fn mk_import(children: ((((String,String),String),Vec<Var>),Option<Typ>)) -> Import {
    Import{ func: (((children.0).0).0).0, module: (((children.0).0).0).1, name: ((children.0).0).1, params: (children.0).1, result: children.1 }
}

fn mk_export(children: (String,String)) -> Export {
    Export{ name: children.0, func: children.1 }
}

fn mk_module(children: (Option<Memory>,ModuleContents)) -> Module {
    Module{ memory: children.0, imports: children.1.imports, exports: children.1.exports, functions: children.1.functions }
}

pub fn parser<C,D>(consumer: C) where C: ParserConsumer<D>, D: Consumer<Module>+ErrConsumer<ParseError> {
    let typ = token_match(is_identifier)
        .map(mk_typ).results();
    let id = token_match(is_identifier)
        .map(mk_id).results();
    let number = token_match(is_number)
        .map(mk_usize).results();
    let text = token_match(is_text)
        .map(mk_string).results();
    let local = token_match(is_begin_local).ignore()
        .and_then(id)
        .zip(typ)
        .and_then(token_match(is_end).ignore())
        .map(mk_var);
    let param = token_match(is_begin_param).ignore()
        .and_then(id)
        .zip(typ)
        .and_then(token_match(is_end).ignore())
        .map(mk_var);
    // A work-around for https://github.com/rust-lang/rust/issues/28229
    // we can't clone param because is_begin_param doesn't implement Clone
    // we can't copy param because it uses zip, which contains a Vec, which isn't copyable.
    let param2 = token_match(is_begin_param).ignore()
        .and_then(id)
        .zip(typ)
        .and_then(token_match(is_end).ignore())
        .map(mk_var);
    let result_typ = token_match(is_begin_result).ignore()
        .and_then(typ)
        .and_then(token_match(is_end).ignore());
    let function = token_match(is_begin_func).ignore()
        .and_then(id)
        .zip(param.star().collect(Vec::new()))
        .zip(result_typ.map(Some).or_emit(None))
        .zip(local.star().collect(Vec::new()))
        .and_then(token_match(is_end).ignore())
        .map(mk_function);
    let segment = token_match(is_begin_segment).ignore()
        .and_then(number)
        .zip(text)
        .and_then(token_match(is_end).ignore())
        .map(mk_segment);
    let memory = token_match(is_begin_memory).ignore()
        .and_then(number)
        .zip(number.map(Some).or_emit(None))
        .zip(segment.star().collect(Vec::new()))
        .and_then(token_match(is_end).ignore())
        .map(mk_memory);
    let import = token_match(is_begin_import).ignore()
        .and_then(id)
        .zip(text)
        .zip(text)
        .zip(param2.star().collect(Vec::new()))
        .zip(result_typ.map(Some).or_emit(None))
        .and_then(token_match(is_end).ignore())
        .map(mk_import);
    let export = token_match(is_begin_export).ignore()
        .and_then(text)
        .zip(id)
        .and_then(token_match(is_end).ignore())
        .map(mk_export);
    let module = token_match(is_begin_module).ignore()
        .and_then(memory.map(Some).or_emit(None))
        .zip(import.or_else(export).or_else(function).star().collect(ModuleContents::new()))
        .and_then(token_match(is_end).ignore())
        .map(mk_module);
    let top_level = module;
    consumer.accept(top_level);
}

#[test]
fn test_parser() {
    use parser::combinators::MatchResult::Matched;
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
                        Begin("segment"),
                            Number(0),
                            Text("abc"),
                        End,
                        Begin("segment"),
                            Number(1),
                            Text("def"),
                        End,
                    End,
                    Begin("import"),
                        Identifier("$foo"),
                        Text("ghi"),
                        Text("jkl"),
                    End,
                    Begin("func"),
                        Identifier("$fish"),
                        Begin("param"),
                            Identifier("$z"),
                            Identifier("i64"),
                        End,
                        Begin("local"),
                            Identifier("$r"),
                            Identifier("i64"),
                        End,
                    End,
                    Begin("export"),
                        Text("fish"),
                        Identifier("$fish"),
                    End,
                    Begin("import"),
                        Identifier("$bar"),
                        Text("ghi"),
                        Text("mno"),
                        Begin("param"),
                            Identifier("$x"),
                            Identifier("f32"),
                        End,
                        Begin("param"),
                            Identifier("$y"),
                            Identifier("f64"),
                        End,
                        Begin("result"),
                            Identifier("i32"),
                        End,
                    End,
                End,
            ];
            let ast = Module{
                memory: Some(Memory{
                    init: 1024,
                    max: None,
                    segments: vec![
                        Segment { addr: 0, data: String::from("abc") },
                        Segment { addr: 1, data: String::from("def") },
                    ],
                }),
                imports: vec![
                    Import {
                        func: String::from("$foo"),
                        module: String::from("ghi"),
                        name: String::from("jkl"),
                        params: vec![],
                        result: None,
                    },
                    Import {
                        func: String::from("$bar"),
                        module: String::from("ghi"),
                        name: String::from("mno"),
                        params: vec![
                            Var{ name: String::from("$x"), typ: F32 },
                            Var{ name: String::from("$y"), typ: F64 },
                        ],
                        result: Some(I32),
                    },
                ],
                exports: vec![
                    Export { name: String::from("fish"), func: String::from("$fish") },
                ],
                functions: vec![
                    Function {
                        name: String::from("$fish"),
                        params: vec![
                            Var{ name: String::from("$z"), typ: I64 },
                        ],
                        result: None,
                        locals: vec![
                            Var{ name: String::from("$r"), typ: I64 },
                        ],
                        body: vec![]
                    },
                ]
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
