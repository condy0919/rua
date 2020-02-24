use std::error;
use std::fmt;
use std::io;
use std::u8;

use phf::phf_map;

use super::from_u8;

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
#[derive(Debug, PartialEq)]
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

    /// Current line number of the source file
    pub fn get_line(&self) -> usize {
        self.line
    }

    /// Gets the next `Token`, or `None` if the end of file reached
    pub fn next(&mut self) -> Result<Option<Token>, LexerError> {
        self.skip_whitespace()?;

        if let Some(c) = self.peek(0)? {
            Ok(Some(match c {
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
                    Some(b'=') | Some(b'[') => return self.read_long_string(),
                    _ => {
                        self.advance(1);
                        Token::LeftBracket
                    }
                },

                b'\"' | b'\'' => return self.read_short_string(),

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
                        todo!("read number")
                    } else {
                        self.advance(1);
                        Token::Dot
                    }
                }

                c if c.is_ascii_digit() => todo!("read number"),
                c if c.is_ascii_alphabetic() || c == b'_' => todo!("read identifier"),
                c => return Err(LexerError::UnexpectedCharacter(c)),
            }))
        } else {
            Ok(None)
        }
    }

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

    pub(crate) fn skip_whitespace(&mut self) -> Result<(), LexerError> {
        while let Some(c) = self.peek(0)? {
            match c {
                b' ' | b'\t' | b'\x0b' | b'\x0c' => {
                    self.advance(1);
                }

                b'\r' | b'\n' => {
                    self.add_new_line()?;
                }

                b'-' => {
                    if self.peek(1)? != Some(b'-') {
                        break;
                    }

                    // comments
                    self.advance(2);
                    match (self.peek(0)?, self.peek(1)?) {
                        (Some(b'['), Some(b'=')) | (Some(b'['), Some(b'[')) => {
                            // TODO read long string
                        }
                        _ => {
                            // short comment, skip until end of line
                            while let Some(c) = self.peek(0)? {
                                if c == b'\r' || c == b'\n' {
                                    break;
                                }
                                self.advance(1);
                            }

                            self.add_new_line()?;
                        }
                    }
                }
                _ => break,
            }
        }

        Ok(())
    }

    pub(crate) fn advance(&mut self, n: usize) {
        assert!(
            n <= self.peek_buf.len(),
            "cannot advance over un-peeked characters"
        );
        self.peek_buf.drain(0..n);
    }

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
