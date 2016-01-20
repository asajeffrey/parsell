use parser::combinators::{Parser, StrParser, ParseTo, Consumer, string, character};
use self::Token::{Begin, End, Identifier, Number, Whitespace};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum Token<'a> {
    Begin(&'a str),
    End,
    Identifier(&'a str),
    Number(usize),
    Whitespace(&'a str),
}

impl<'a> From<Token<'a>> for String {
    fn from(tok: Token<'a>) -> String {
        match tok {
            Begin(kw)     => String::from("(") + kw,
            End           => String::from(")"),
            Identifier(x) => String::from(x),
            Number(n)     => n.to_string(),
            Whitespace(s) => String::from(s),
        }
    }
}

pub trait LexerConsumer<D> where D: for<'a> Consumer<Token<'a>> {
    fn accept<L>(self, lexer: L) where L: for<'a> ParseTo<&'a str,D>;
}

fn is_lparen(ch: char) -> bool { ch == '(' }
fn is_rparen(ch: char) -> bool { ch == ')' }
fn is_dollar(ch: char) -> bool { ch == '$' }
fn is_keyword_char(ch: char) -> bool { ch.is_alphanumeric() || (ch == '.') }
fn is_identifier_char(ch: char) -> bool { ch.is_alphanumeric() || (ch == '.') || (ch == '$') }

fn mk_begin<'a>(s: &'a str) -> Token<'a> { Begin(s) }
fn mk_end<'a>(ch: char) -> Token<'a> { End }
fn mk_identifier<'a>(s: &'a str) -> Token<'a> { Identifier(s) }
fn mk_number<'a>(s: &'a str) -> Token<'a> { Number(usize::from_str_radix(s,10).unwrap()) }
fn mk_whitespace<'a>(s: &'a str) -> Token<'a> { Whitespace(s) }

#[allow(non_snake_case)]
pub fn lexer<C,D>(consumer: C) where C: LexerConsumer<D>, D: for<'a> Consumer<Token<'a>> {
    let BEGIN = character(is_lparen).ignore().and_then(character(is_keyword_char).plus().buffer().map(mk_begin));
    let END = character(is_rparen).map(mk_end);
    let WHITESPACE = character(char::is_whitespace).plus().buffer().map(mk_whitespace);
    let IDENTIFIER = character(is_identifier_char).plus().buffer().map(mk_identifier);
    let NUMBER = character(char::is_numeric).plus().buffer().map(mk_number);
    consumer.accept(BEGIN.or_else(END).or_else(IDENTIFIER).or_else(NUMBER).or_else(WHITESPACE).star())
}

#[test]
fn test_lexer() {
    struct TestConsumer(Vec<String>);
    impl<'a> Consumer<Token<'a>> for TestConsumer {
        fn accept(&mut self, tok: Token<'a>) {
            self.0.push(String::from(tok));
        }
    }
    impl LexerConsumer<TestConsumer> for TestConsumer {
        fn accept<L>(mut self, mut lex: L) where L: for<'a> ParseTo<&'a str,TestConsumer> {
            lex.push_to("(a123 $bcd f32 \t 37)", &mut self);
            assert_eq!(self.0, vec!["(a123", " ", "$bcd", " ", "f32", " \t ", "37", ")"]);
        }
    }
    lexer(TestConsumer(Vec::new()));
}
