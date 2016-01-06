use std::mem;

// Borrowing encoding of paramaterized types from
// https://github.com/rust-lang/rfcs/blob/master/text/0195-associated-items.md#encoding-higher-kinded-types

pub trait RefType<'a> {
    type Ref;
}

pub type Ref<'a,T> where T: RefType<'a> = T::Ref;

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub enum PushResult<T> {
    WillMatch,
    MightMatch,
    WontMatch,
    MatchedAll,
    MatchedSome(T),
}

pub trait Listener<T> where T: for<'a> RefType<'a> {
    fn push<'a,'b>(&'a mut self, value: Ref<'b,T>) -> PushResult<Ref<'b,T>>;
    fn done(&mut self);
}

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

impl<T> Listener<StrRef> for WhitespaceParser<T> where T: Listener<StrRef> {
    fn push<'a,'b>(&'a mut self, string: &'b str) -> PushResult<&'b str> {
        match mem::replace(&mut self.state, WhitespaceParserState::End) {
            WhitespaceParserState::Beginning => {
                match string.chars().next() {
                    None => {
                        self.state = WhitespaceParserState::Beginning;
                        PushResult::MightMatch
                    },
                    Some(ch) if ch.is_whitespace() => {
                        let len = ch.len_utf8();
                        match string[len..].find(|ch: char| !ch.is_whitespace()) {
                            None => {
                                self.state = WhitespaceParserState::Middle(String::from(string));
                                PushResult::WillMatch
                            },
                            Some(index) => {
                                self.downstream.push(&string[0..index+len]);
                                if string.len() == index+len {
                                    PushResult::MatchedAll
                                } else {
                                    PushResult::MatchedSome(&string[index+len..])
                                }
                            }
                        }
                    },
                    Some(_) => PushResult::WontMatch,
                }
            },
            WhitespaceParserState::Middle(mut buffer) => {
                match string.find(|ch: char| !ch.is_whitespace()) {
                    None => {
                        buffer.push_str(string);
                        self.state = WhitespaceParserState::Middle(buffer);
                        PushResult::WillMatch
                    },
                    Some(index) => {
                        buffer.push_str(&string[0..index]);
                        self.downstream.push(&*buffer);
                        if string.len() == index {
                            PushResult::MatchedAll
                        } else {
                            PushResult::MatchedSome(&string[index..])
                        }
                    }
                }
            },
            WhitespaceParserState::End => PushResult::MatchedSome(string),
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

impl Listener<StrRef> for String {
    fn push<'a,'b>(&'a mut self, string: &'b str) -> PushResult<&'b str> {
        self.push_str(string);
        PushResult::MatchedAll
    }
    fn done(&mut self) {
    }
}

#[test]
fn test_whitespace() {
    let buffer = String::from("");
    let mut parser = WhitespaceParser::from(buffer);
    assert_eq!(parser.push(" \r\n\t"), PushResult::WillMatch);
    assert_eq!(parser.downstream, "");
    assert_eq!(parser.push(" stuff"), PushResult::MatchedSome("stuff"));
    assert_eq!(parser.downstream, " \r\n\t ");
}
