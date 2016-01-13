use parser::combinators::{Parser, StrParser, ParseTo, Consumer, string, character};
use self::Token::{LParen, RParen, Whitespace, Identifier};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum Token<'a> {
    LParen,
    RParen,
    Whitespace,
    Identifier(&'a str),
}

pub trait LexerConsumer<D> where D: for<'a> Consumer<Token<'a>> {
    fn accept<L>(self, lexer: L) where L: for<'a> ParseTo<&'a str,D>;
}

fn mk_identifier<'a>(s: &'a str) -> Token<'a> { Identifier(s) }

#[allow(non_snake_case)]
pub fn lexer<C,D>(consumer: C) where C: LexerConsumer<D>, D: for<'a> Consumer<Token<'a>> {
    let LPAREN = string("(").map(|_| LParen);
    let RPAREN = string(")").map(|_| RParen);
    let WHITESPACE = character(char::is_whitespace).map(|_| Whitespace);
    let IDENTIFIER = character(char::is_alphabetic).and_then(character(char::is_alphanumeric).star())
                                                   .buffer().map(mk_identifier);
    let TOKEN = LPAREN.or_else(RPAREN).or_else(WHITESPACE).or_else(IDENTIFIER);
    consumer.accept(TOKEN.star())
}


#[test]
fn test_lexer() {
    impl<'a> Consumer<Token<'a>> for Vec<Token<'static>> {
        fn accept(&mut self, token: Token<'a>) {
            assert_eq!(self.remove(0), token);
        }
    }
    struct TestConsumer;
    impl<'a> LexerConsumer<Vec<Token<'static>>> for TestConsumer {
        fn accept<P>(self, mut lex: P) where P: ParseTo<&'a str,Vec<Token<'static>>> {
            let mut tokens = vec![LParen, Identifier("a123"), Whitespace, Whitespace, Identifier("bcd"), RParen];
            lex.push_to("(a123  bcd)", &mut tokens);
            assert_eq!(tokens, []);
        }
    }
    lexer(TestConsumer);
}
