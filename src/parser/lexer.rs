use parser::combinators::{Parser, StrParser, Consumer, ParserConsumer, string, character};
use self::Token::{LParen, RParen, Whitespace, Identifier};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum Token<'a> {
    LParen,
    RParen,
    Whitespace,
    Identifier(&'a str),
}

fn mk_identifier<'a>(s: &'a str) -> Token<'a> { Identifier(s) }

#[allow(non_snake_case)]
pub fn lexer<C,D>(consumer: &mut C) where C: for<'a> ParserConsumer<&'a str,D>, D: for<'a> Consumer<Token<'a>> {
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
    use parser::combinators::ParseTo;
    impl<'a> Consumer<Token<'a>> for Vec<Token<'static>> {
        fn accept(&mut self, token: Token<'a>) {
            assert_eq!(self.remove(0), token);
        }
    }
    struct TestConsumer;
    impl<'a> ParserConsumer<&'a str, Vec<Token<'static>>> for TestConsumer {
        fn accept<P>(&mut self, mut lex: P) where P: ParseTo<&'a str,Vec<Token<'static>>> {
            let mut tokens = vec![LParen, Identifier("a123"), Whitespace, Whitespace, Identifier("bcd"), RParen];
            lex.push_to("(a123  bcd)", &mut tokens);
            assert_eq!(tokens, []);
        }
    }
    lexer(&mut TestConsumer);
}
