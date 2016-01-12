use parser::combinators::{TypeWithLifetime, Str, Unit, Function, Parser, StrParser, ParserConsumer, string, character};
use self::TokenAt::{LParen, RParen, Whitespace, Identifier};

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum TokenAt<'a> {
    LParen,
    RParen,
    Whitespace,
    Identifier(&'a str),
}

pub struct Token;

impl<'a> TypeWithLifetime<'a> for Token {
    type Type = TokenAt<'a>;
}

impl Function<Unit,Token> for TokenAt<'static> {
    fn apply<'a>(&self, _: ()) -> TokenAt<'a> {
        self.clone()
    }
}

struct MkIdentifier;

impl Function<Str,Token> for MkIdentifier {
    fn apply<'a>(&self, name: &'a str) -> TokenAt<'a> {
        Identifier(name)
    }
}

#[allow(non_snake_case)]
pub fn lexer<C>(consumer: &mut C) where C: ParserConsumer<Str,Token> {
    let LPAREN = string("(").map(LParen);
    let RPAREN = string(")").map(RParen);
    let WHITESPACE = character(char::is_whitespace).plus().map(Whitespace);
    let IDENTIFIER = character(char::is_alphabetic).and_then(character(char::is_alphanumeric).star()).buffer().map(MkIdentifier);
    let TOKEN = LPAREN.or_else(RPAREN).or_else(WHITESPACE).or_else(IDENTIFIER);
    consumer.accept(TOKEN.star())
}

