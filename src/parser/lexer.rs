use parser::combinators::{TypeWithLifetime, Str, Unit, Function, Parser, StrParser, Consumer, ParserConsumer, string, character};
use self::TokenAt::{LParen, RParen, Whitespace, Identifier};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
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
    let WHITESPACE = character(char::is_whitespace).map(Whitespace);
    let IDENTIFIER = character(char::is_alphabetic).and_then(character(char::is_alphanumeric).star()).buffer().map(MkIdentifier);
    let TOKEN = LPAREN.or_else(RPAREN).or_else(WHITESPACE).or_else(IDENTIFIER);
    consumer.accept(TOKEN.star())
}


#[test]
fn test_lexer() {
    impl Consumer<Token> for Vec<TokenAt<'static>> {
        fn accept<'a>(&mut self, token: TokenAt<'a>) {
            assert_eq!(self.remove(0), token);
        }
    }
    struct TestConsumer;
    impl ParserConsumer<Str,Token> for TestConsumer {
        fn accept<P>(&mut self, mut lex: P) where P: Parser<Str,Token> {
            let mut tokens = vec![LParen, Identifier("a123"), Whitespace, Whitespace, Identifier("bcd"), RParen];
            lex.push_to("(a123  bcd)", &mut tokens);
            assert_eq!(tokens, []);
        }
    }
    lexer(&mut TestConsumer);
}
