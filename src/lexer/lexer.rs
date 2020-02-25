use std::error;
use std::fmt;
use std::io;
use std::u8;

use phf::phf_map;

use super::from_u8;

/// Lua keywords are reserved and cannot be used as an idenfitier.
const LUA_KEYWORDS: phf::Map<&'static str, Token> = phf_map! {
    "and" => Token::And,
    "break" => Token::Break,
    "do" => Token::Do,
    "else" => Token::Else,
    "elseif" => Token::ElseIf,
    "end" => Token::End,
    "false" => Token::False,
    "for" => Token::For,
    "function" => Token::Function,
    "goto" => Token::Goto,
    "if" => Token::If,
    "in" => Token::In,
    "local" => Token::Local,
    "nil" => Token::Nil,
    "not" => Token::Not,
    "or" => Token::Or,
    "repeat" => Token::Repeat,
    "return" => Token::Return,
    "then" => Token::Then,
    "true" => Token::True,
    "until" => Token::Until,
    "while" => Token::While,
};

///
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    And,
    Break,
    Do,
    Else,
    ElseIf,
    End,
    False,
    For,
    Function,
    Goto,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,
    Add,
    Minus,
    Mul,
    Div,
    IDiv,
    Power,
    Mod,
    BitXorNot,
    BitAnd,
    BitOr,
    ShiftRight,
    ShiftLeft,
    LessThan,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    Assign,
    Len,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Colon,
    SemiColon,
    DoubleColon,
    Comma,
    Dot,
    Concat,
    Dots,
    Identifier(String),
    String(String),
    Integer(i64),
    Number(f64),
    None,
}

#[derive(Debug, PartialEq)]
pub enum LexerError {
    UnfinishedShortString(u8),
    UnfinishedLongString,
    UnexpectedCharacter(u8),
    HexDigitExpected,
    EscapeUnicodeStart,
    EscapeUnicodeEnd,
    EscapeUnicodeInvalid,
    EscapeDecimalTooLarge,
    EscapeDecimalInvalid,
    InvalidEscape,
    InvalidLongStringDelimiter,
    BadNumber,
    IOErrorKind(io::ErrorKind),
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LexerError::UnfinishedShortString(c) => write!(
                f,
                "short string not finished, expected matching {}",
                from_u8(*c)
            ),
            LexerError::UnfinishedLongString => write!(f, "unfinished long string"),
            LexerError::UnexpectedCharacter(c) => {
                write!(f, "unexpected character: '{}'", from_u8(*c))
            }
            LexerError::HexDigitExpected => write!(f, "hexdecimal digit expected"),
            LexerError::EscapeUnicodeStart => write!(f, "missing '{{' in \\u{{xxxx}} escape"),
            LexerError::EscapeUnicodeEnd => write!(f, "missing '}}' in \\u{{xxxx}} escape"),
            LexerError::EscapeUnicodeInvalid => {
                write!(f, "invalid unicode value in \\u{{xxxx}} escape")
            }
            LexerError::EscapeDecimalTooLarge => write!(f, "\\ddd escape out of 0-255 range"),
            LexerError::EscapeDecimalInvalid => write!(f, "\\ddd escape format error"),
            LexerError::InvalidEscape => write!(f, "invalid escape sequence"),
            LexerError::InvalidLongStringDelimiter => write!(f, "invalid long string delimiter"),
            LexerError::BadNumber => write!(f, "malformed number"),
            LexerError::IOErrorKind(e) => write!(f, "IO ErrorKind: {:?}", e),
        }
    }
}

impl error::Error for LexerError {}

/// Lexer
pub struct Lexer<'a, S: io::Read> {
    src: &'a mut S,
    peek_buf: Vec<u8>,
    line: usize,
}

impl<'a, S: io::Read> Lexer<'a, S> {
    /// Creates a new `Lexer`
    pub fn new(src: &'a mut S) -> Lexer<'a, S> {
        Lexer {
            src,
            peek_buf: Vec::new(),
            line: 1,
        }
    }

    /// Current line number of the source file, 1-indexed
    pub fn get_line(&self) -> usize {
        self.line
    }

    /// Gets the next `Token`, or `Token::None` if the end of file reached
    pub fn next(&mut self) -> Result<Token, LexerError> {
        self.skip_whitespace()?;

        Ok(if let Some(c) = self.peek(0)? {
            match c {
                b'(' | b')' | b'{' | b'}' | b']' | b'+' | b'-' | b'*' | b'%' | b'^' | b'#'
                | b'&' | b'|' | b';' | b',' => {
                    self.advance(1);
                    match c {
                        b'(' => Token::LeftParen,
                        b')' => Token::RightParen,
                        b'{' => Token::LeftBrace,
                        b'}' => Token::RightParen,
                        b']' => Token::RightBracket,
                        b'+' => Token::Add,
                        b'-' => Token::Minus,
                        b'*' => Token::Mul,
                        b'%' => Token::Mod,
                        b'^' => Token::Power,
                        b'#' => Token::Concat,
                        b'&' => Token::BitAnd,
                        b'|' => Token::BitOr,
                        b';' => Token::SemiColon,
                        b',' => Token::Comma,
                        _ => unreachable!(),
                    }
                }

                b'/' => {
                    self.advance(1);
                    if self.peek(0)? == Some(b'/') {
                        self.advance(1);
                        Token::IDiv
                    } else {
                        Token::Div
                    }
                }

                b'~' => {
                    self.advance(1);
                    if self.peek(0)? == Some(b'=') {
                        self.advance(1);
                        Token::NotEqual
                    } else {
                        Token::BitXorNot
                    }
                }

                b'[' => match self.peek(1)? {
                    Some(b'=') | Some(b'[') => {
                        return self.read_long_string();
                    }
                    _ => {
                        self.advance(1);
                        Token::LeftBracket
                    }
                },

                b'\"' | b'\'' => {
                    return self.read_short_string();
                }

                b'=' => {
                    self.advance(1);
                    if self.peek(0)? == Some(b'=') {
                        self.advance(1);
                        Token::Equal
                    } else {
                        Token::Assign
                    }
                }

                b'<' => {
                    self.advance(1);
                    match self.peek(0)? {
                        Some(c) if c == b'=' || c == b'<' => {
                            self.advance(1);
                            match c {
                                b'=' => Token::LessEqual,
                                _ => Token::ShiftRight,
                            }
                        }
                        _ => Token::LessThan,
                    }
                }

                b'>' => {
                    self.advance(1);
                    match self.peek(0)? {
                        Some(c) if c == b'=' || c == b'>' => {
                            self.advance(1);
                            match c {
                                b'=' => Token::GreaterEqual,
                                _ => Token::ShiftRight,
                            }
                        }
                        _ => Token::GreaterEqual,
                    }
                }

                b':' => {
                    self.advance(1);
                    if self.peek(0)? == Some(b':') {
                        self.advance(1);
                        Token::DoubleColon
                    } else {
                        Token::Colon
                    }
                }

                b'.' => {
                    if self.peek(1)? == Some(b'.') {
                        if self.peek(2)? == Some(b'.') {
                            self.advance(3);
                            Token::Dots
                        } else {
                            self.advance(2);
                            Token::Concat
                        }
                    } else if self
                        .peek(1)?
                        .as_ref()
                        .map(u8::is_ascii_digit)
                        .unwrap_or(false)
                    {
                        return self.read_numeral();
                    } else {
                        self.advance(1);
                        Token::Dot
                    }
                }

                c if c.is_ascii_digit() => {
                    return self.read_numeral();
                }

                c if c.is_ascii_alphabetic() || c == b'_' => {
                    // TODO optimize frequent call of `from_u8`.
                    let mut string_buf = String::new();
                    string_buf.push(from_u8(c));
                    self.advance(1);

                    while let Some(c) = self.peek(0)? {
                        if c.is_ascii_alphanumeric() || c == b'_' {
                            string_buf.push(from_u8(c));
                            self.advance(1);
                        } else {
                            break;
                        }
                    }

                    if let Some(keyword) = LUA_KEYWORDS.get(string_buf.as_str()) {
                        keyword.clone()
                    } else {
                        Token::Identifier(string_buf)
                    }
                }

                c => return Err(LexerError::UnexpectedCharacter(c)),
            }
        } else {
            Token::None
        })
    }

    /// Peeks n-bytes ahead
    pub(crate) fn peek(&mut self, n: usize) -> Result<Option<u8>, LexerError> {
        while self.peek_buf.len() <= n {
            let mut c = [0];
            match self.src.read(&mut c) {
                Ok(0) => {
                    break;
                }
                Ok(_) => {
                    self.peek_buf.push(c[0]);
                }
                Err(e) => {
                    if e.kind() != io::ErrorKind::Interrupted {
                        return Err(LexerError::IOErrorKind(e.kind()));
                    }
                }
            }
        }

        Ok(self.peek_buf.get(n).cloned())
    }

    /// Skips all whitespaces, including line breaks.
    pub(crate) fn skip_whitespace(&mut self) -> Result<(), LexerError> {
        while let Some(c) = self.peek(0)? {
            match c {
                ws if ws.is_ascii_whitespace() => {
                    if ws == b'\r' || ws == b'\n' {
                        self.add_new_line()?;
                    } else {
                        self.advance(1);
                    }
                }

                b'#' if self.get_line() == 1 => {
                    // shebang, skip until end of line.
                    self.advance(1);
                    self.skip_until_eol()?;
                }

                b'-' => {
                    if self.peek(1)? != Some(b'-') {
                        break;
                    }

                    self.advance(2);
                    match (self.peek(0)?, self.peek(1)?) {
                        (Some(b'['), Some(b'=')) | (Some(b'['), Some(b'[')) => {
                            // long comment, read and ignore the result
                            self.read_long_string()?;
                        }
                        _ => {
                            // short comment, skip until end of line
                            self.skip_until_eol()?;
                        }
                    }
                }
                _ => break,
            }
        }

        Ok(())
    }

    /// Skips the whole line
    pub(crate) fn skip_until_eol(&mut self) -> Result<(), LexerError> {
        while let Some(c) = self.peek(0)? {
            if c == b'\r' || c == b'\n' {
                self.add_new_line()?;
                break;
            }
            self.advance(1);
        }
        Ok(())
    }

    /// Skips n-bytes
    pub(crate) fn advance(&mut self, n: usize) {
        assert!(
            n <= self.peek_buf.len(),
            "cannot advance over un-peeked characters"
        );
        self.peek_buf.drain(0..n);
    }

    /// Starts a newline if it encouters `\r` or `\n`.
    ///
    /// See comments below for details.
    pub(crate) fn add_new_line(&mut self) -> Result<(), LexerError> {
        let c = self.peek(0)?.unwrap();
        assert!(c == b'\r' || c == b'\n');

        // Any kind of end-of-line sequence (carriage return, newline, carriage
        // return followed by newline, or newline followed by carriage return)
        // is converted to a simple newline.
        self.line += 1;
        self.advance(1);
        if let Some(next_char) = self.peek(0)? {
            if c == b'\n' && next_char == b'\r' || c == b'\r' && next_char == b'\n' {
                self.advance(1);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whitespace_short_comment() {
        let mut s: &[u8] = b"   -- text in comments\n'string'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::String("string".to_owned()));
        assert_eq!(lex.get_line(), 2);
    }

    #[test]
    fn whitespace_long_comment() {
        let mut s: &[u8] =
            b"--[[ text in long comments\nstill in comments\n]]\n'string after long comments'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap(),
            Token::String("string after long comments".to_owned())
        );
        assert_eq!(lex.get_line(), 4);
    }

    #[test]
    fn whitespace_shebang() {
        let mut s: &[u8] = b"#!/bin/lua arguments will be ignored\n 'string'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::String("string".to_owned()));
        assert_eq!(lex.get_line(), 2);
    }

    #[test]
    fn keywords() {
        let mut s: &[u8] = b"and break do else elseif end false for function goto \
                             if in local nil not or repeat return then true until while";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::And);
        assert_eq!(lex.next().unwrap(), Token::Break);
        assert_eq!(lex.next().unwrap(), Token::Do);
        assert_eq!(lex.next().unwrap(), Token::Else);
        assert_eq!(lex.next().unwrap(), Token::ElseIf);
        assert_eq!(lex.next().unwrap(), Token::End);
        assert_eq!(lex.next().unwrap(), Token::False);
        assert_eq!(lex.next().unwrap(), Token::For);
        assert_eq!(lex.next().unwrap(), Token::Function);
        assert_eq!(lex.next().unwrap(), Token::Goto);
        assert_eq!(lex.next().unwrap(), Token::If);
        assert_eq!(lex.next().unwrap(), Token::In);
        assert_eq!(lex.next().unwrap(), Token::Local);
        assert_eq!(lex.next().unwrap(), Token::Nil);
        assert_eq!(lex.next().unwrap(), Token::Not);
        assert_eq!(lex.next().unwrap(), Token::Or);
        assert_eq!(lex.next().unwrap(), Token::Repeat);
        assert_eq!(lex.next().unwrap(), Token::Return);
        assert_eq!(lex.next().unwrap(), Token::Then);
        assert_eq!(lex.next().unwrap(), Token::True);
        assert_eq!(lex.next().unwrap(), Token::Until);
        assert_eq!(lex.next().unwrap(), Token::While);
        assert_eq!(lex.next().unwrap(), Token::None);
    }

    #[test]
    fn identifiers() {
        let mut s: &[u8] = b"usual identifiers except function";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::Identifier("usual".to_owned()));
        assert_eq!(
            lex.next().unwrap(),
            Token::Identifier("identifiers".to_owned())
        );
        assert_eq!(lex.next().unwrap(), Token::Identifier("except".to_owned()));
        assert_eq!(lex.next().unwrap(), Token::Function);
    }
}
