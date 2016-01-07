use std::mem;

// ----------- Types for streaming -------------

// Borrowing encoding of paramaterized types from
// https://github.com/rust-lang/rfcs/blob/master/text/0195-associated-items.md#encoding-higher-kinded-types

pub trait RefType<'a> {
    type Ref;
}

pub type Ref<'a,T> where T: RefType<'a> = T::Ref;

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum MatchResult<T> {
    WillMatch,
    MightMatch,
    WontMatch,
    MatchedAll,
    MatchedSome(T),
}

pub trait Matcher<T> where T: for<'a> RefType<'a> {
    fn push<'a,'b>(&'a mut self, value: Ref<'b,T>) -> MatchResult<Ref<'b,T>>;
    fn done(&mut self);
}

// ----------- Types for streaming -------------

pub struct StrRef;

impl<'a> RefType<'a> for StrRef {
    type Ref = &'a str;
}

enum WhitespaceParserState {
    Beginning,
    Middle(String),
    End,
}

struct WhitespaceParser<T> {
    downstream: T,    
    state: WhitespaceParserState,
}

impl<T> From<T> for WhitespaceParser<T> {
    fn from(downstream: T) -> WhitespaceParser<T> {
        WhitespaceParser{ downstream: downstream, state: WhitespaceParserState::Beginning }
    }
}

impl<T> Matcher<StrRef> for WhitespaceParser<T> where T: Matcher<StrRef> {
    fn push<'a,'b>(&'a mut self, string: &'b str) -> MatchResult<&'b str> {
        match mem::replace(&mut self.state, WhitespaceParserState::End) {
            WhitespaceParserState::Beginning => {
                match string.chars().next() {
                    None => {
                        self.state = WhitespaceParserState::Beginning;
                        MatchResult::MightMatch
                    },
                    Some(ch) if ch.is_whitespace() => {
                        let len = ch.len_utf8();
                        match string[len..].find(|ch: char| !ch.is_whitespace()) {
                            None => {
                                self.state = WhitespaceParserState::Middle(String::from(string));
                                MatchResult::WillMatch
                            },
                            Some(index) => {
                                self.downstream.push(&string[0..index+len]);
                                if string.len() == index+len {
                                    MatchResult::MatchedAll
                                } else {
                                    MatchResult::MatchedSome(&string[index+len..])
                                }
                            }
                        }
                    },
                    Some(_) => MatchResult::WontMatch,
                }
            },
            WhitespaceParserState::Middle(mut buffer) => {
                match string.find(|ch: char| !ch.is_whitespace()) {
                    None => {
                        buffer.push_str(string);
                        self.state = WhitespaceParserState::Middle(buffer);
                        MatchResult::WillMatch
                    },
                    Some(index) => {
                        buffer.push_str(&string[0..index]);
                        self.downstream.push(&*buffer);
                        if string.len() == index {
                            MatchResult::MatchedAll
                        } else {
                            MatchResult::MatchedSome(&string[index..])
                        }
                    }
                }
            },
            WhitespaceParserState::End => MatchResult::MatchedSome(string),
        }
    }
    fn done(&mut self) {
        match mem::replace(&mut self.state, WhitespaceParserState::End) {
            WhitespaceParserState::Middle(buffer) => {
                self.downstream.push(&*buffer);
            },
            _              => (),
        }
        self.downstream.done();
    }
}

impl Matcher<StrRef> for String {
    fn push<'a,'b>(&'a mut self, string: &'b str) -> MatchResult<&'b str> {
        self.push_str(string);
        MatchResult::MatchedAll
    }
    fn done(&mut self) {
    }
}

#[test]
fn test_whitespace() {
    let buffer = String::from("");
    let mut parser = WhitespaceParser::from(buffer);
    assert_eq!(parser.push(" \r\n\t"), MatchResult::WillMatch);
    assert_eq!(parser.downstream, "");
    assert_eq!(parser.push(" stuff"), MatchResult::MatchedSome("stuff"));
    assert_eq!(parser.downstream, " \r\n\t ");
}
