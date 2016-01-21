use parser::combinators::{Parser, ParseTo, Consumer, ErrConsumer, character, character_match};
use self::Token::{Begin, End, Identifier, Number, Text, Whitespace};
use self::LexError::{ShouldntHappen};
use std::num::ParseIntError;

#[derive(Copy, Clone, Eq, Hash, Ord, PartialOrd, Debug)]
pub enum Token<'a> {
    Begin(&'a str),
    End,
    Identifier(&'a str),
    Number(usize),
    Text(&'a str),
    Whitespace(&'a str),
}

impl<'a,'b> PartialEq<Token<'a>> for Token<'b> {
    fn eq(&self, other: &Token<'a>) -> bool {
        match (*self, *other) {
            (Begin(s),      Begin(t))      => s == t,
            (End,           End)           => true,
            (Identifier(x), Identifier(y)) => x == y,
            (Number(m),     Number(n))     => m == n,
            (Text(s),       Text(t))       => s == t,
            (Whitespace(s), Whitespace(t)) => s == t,
            _                              => false,
        }
    }
}

impl<'a> From<Token<'a>> for String {
    fn from(tok: Token<'a>) -> String {
        match tok {
            Begin(kw)     => String::from("(") + kw,
            End           => String::from(")"),
            Identifier(x) => String::from(x),
            Number(n)     => n.to_string(),
            Text(s)       => String::from("\"") + s + "\"",
            Whitespace(s) => String::from(s),
        }
    }
}

#[derive(Clone, Debug)]
pub enum LexError {
    ShouldntHappen(ParseIntError),
}

impl From<ParseIntError> for LexError {
    fn from(err: ParseIntError) -> LexError {
        ShouldntHappen(err)
    }
}

pub trait LexerConsumer<D> where D: ErrConsumer<LexError>+for<'a> Consumer<Token<'a>> {
    fn accept<L>(self, lexer: L) where L: for<'a> ParseTo<&'a str,D>;
}

fn is_keyword_char(ch: char) -> bool { ch.is_alphanumeric() || (ch == '.') }
fn is_identifier_char(ch: char) -> bool { ch.is_alphanumeric() || (ch == '.') || (ch == '$') }
fn is_unescaped_char(ch: char) -> bool { ch != '"' && ch != '\\' && ch != '\r' && ch != '\n' }
fn is_escape_char(ch: char) -> bool { ch == 'n' || ch == 'r' || ch == 't' || ch == '\\' || ch == '"' || ch == '\'' }
                                     
fn mk_begin<'a>(s: &'a str) -> Token<'a> { Begin(s) }
fn mk_end<'a>(_: char) -> Token<'a> { End }
fn mk_identifier<'a>(s: &'a str) -> Token<'a> { Identifier(s) }
fn mk_number<'a>(s: &'a str) -> Result<Token<'a>,LexError> { Ok(Number(try!(usize::from_str_radix(s,10)))) }
fn mk_text<'a>(s: &'a str) -> Token<'a> { Text(s) }
fn mk_whitespace<'a>(s: &'a str) -> Token<'a> { Whitespace(s) }

#[allow(non_snake_case)]
pub fn lexer<C,D>(consumer: C) where C: LexerConsumer<D>, D: ErrConsumer<LexError>+for<'a> Consumer<Token<'a>> {
    let BEGIN = character('(').ignore()
        .and_then(character_match(is_keyword_char).plus().buffer())
        .map(mk_begin);
    let END = character(')')
        .map(mk_end);
    let WHITESPACE = character_match(char::is_whitespace).plus().buffer()
        .map(mk_whitespace);
    let IDENTIFIER = character_match(is_identifier_char).plus().buffer()
        .map(mk_identifier);
    let NUMBER = character_match(char::is_numeric).plus().buffer()
        .map(mk_number).results();
    let CHAR = character_match(is_unescaped_char)
        .or_else(character('\\').and_then(character_match(is_escape_char)));
    let TEXT = character('"').ignore()
        .and_then(CHAR.star().buffer())
        .and_then(character('"').ignore())
        .map(mk_text);
    let TOKEN = BEGIN
        .or_else(END)
        .or_else(IDENTIFIER)
        .or_else(NUMBER)
        .or_else(TEXT)
        .or_else(WHITESPACE);
    consumer.accept(TOKEN.star())
}

#[test]
fn test_lexer() {
    struct TestConsumer(Vec<String>,Vec<LexError>);
    impl<'a> Consumer<Token<'a>> for TestConsumer {
        fn accept(&mut self, tok: Token<'a>) {
            self.0.push(String::from(tok));
        }
    }
    impl ErrConsumer<LexError> for TestConsumer {
        fn error(&mut self, err: LexError) {
            self.1.push(err);
        }
    }
    impl LexerConsumer<TestConsumer> for TestConsumer {
        fn accept<L>(mut self, mut lex: L) where L: for<'a> ParseTo<&'a str,TestConsumer> {
            lex.push_to("(a123 $bcd f32 \t \"cd\\r\\nef\\\"gh\" 37)", &mut self);
            assert_eq!(self.0, ["(a123", " ", "$bcd", " ", "f32", " \t ", "\"cd\\r\\nef\\\"gh\"", " ", "37", ")"]);
            assert_eq!(self.1.len(), 0);
        }
    }
    lexer(TestConsumer(Vec::new(),Vec::new()));
}
