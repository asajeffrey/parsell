use parser::combinators::{TypeWithLifetime, At, Str, Unit, Parser, StringParser, string, character};

pub enum TokenAt<'a> {
    LParen,
    RParen,
    Whitespace,
    Identifier(&'a str),
}

pub struct Token;

impl<'a> TypeWithLifetime<'a> for TokenAt<'a> {
    type Type = TokenAt<'a>;
}

fn foo() {
    let LPAREN = string("(");
    let RPAREN = string(")");
    let WHITESPACE = character(char::is_whitespace).plus();
    let IDENTIFIER = character(char::is_alphabetic).and_then(character(char::is_alphanumeric).star());
}

