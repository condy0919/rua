use std::error;
use std::fmt;
use std::io;
use std::rc::Rc;

use crate::lexer::{Lexer, LexerError, Token};

/// ParserError
///
/// There are 6 errors when parsing:
///
/// - `Unexpected` token encountered
/// - `EndOfStream` early ended
/// - `AssignToExpression` invalid assignment
/// - `ExpressionNotStatement` SuffixedExpression needed
/// - `RecursionLimit` the recursion depth deeper than `MAX_RECURSION`
/// - `LexerError` lexer level error
#[derive(Debug, PartialEq)]
pub enum ParserError {
    Unexpected {
        unexpected: String,
        expected: Option<String>,
    },
    EndOfStream {
        expected: Option<String>,
    },
    AssignToExpression,
    ExpressionNotStatement,
    RecursionLimit,
    LexerError(LexerError),
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParserError::Unexpected {
                unexpected,
                expected,
            } => {
                write!(f, "found {:?}", unexpected)?;
                if let Some(s) = expected {
                    write!(f, ", expected {}", s)?;
                }
                Ok(())
            }

            ParserError::EndOfStream { expected } => {
                write!(f, "unexpected end of token stream")?;
                if let Some(s) = expected {
                    write!(f, ", expected {}", s)?;
                }
                Ok(())
            }

            ParserError::AssignToExpression => write!(f, "cannot assign to expression"),
            ParserError::ExpressionNotStatement => write!(f, "expression is not a statement"),
            ParserError::RecursionLimit => write!(f, "recursion limit reached"),
            ParserError::LexerError(e) => write!(f, "{}", e),
        }
    }
}

impl error::Error for ParserError {}

/// Parser
///
/// It implements a recursive decent parser.
///
/// Visit https://en.wikipedia.org/wiki/Recursive_descent_parser for more
/// information.
pub struct Parser<'a, S: io::Read> {
    lexer: Lexer<'a, S>,
    tokens: Vec<Token>,
    recursion_guard: Rc<()>,
}

impl<'a, S: io::Read> Parser<'a, S> {
    /// Creates a new `Parser`
    pub fn new(src: &'a mut S) -> Parser<'a, S> {
        Parser {
            lexer: Lexer::new(src),
            tokens: Vec::new(),
            recursion_guard: Rc::new(()),
        }
    }

    /// Error if we have more than **MAX_RECURSION** guards live, otherwise
    /// return a new recursion guard (a recursion guard is just an `Rc` used
    /// solely for its live count).
    pub(crate) fn get_recursion_guard(&mut self) -> Result<Rc<()>, ParserError> {
        // Maximum depth for nested function calls and syntactical nested
        // non-terminals in a program.
        const MAX_RECURSION: usize = 200;
        if Rc::strong_count(&self.recursion_guard) < MAX_RECURSION {
            Ok(self.recursion_guard.clone())
        } else {
            Err(ParserError::RecursionLimit)
        }
    }

    /// Consumes the next token, returning an error if it's not a string or
    /// yielding it
    pub(crate) fn expect_string(&mut self) -> Result<String, ParserError> {
        match self.peek(0)? {
            Some(&Token::String(ref s)) => {
                let s2 = s.clone();
                self.advance(1);
                Ok(s2)
            }
            None => Err(ParserError::EndOfStream {
                expected: Some("string".to_owned()),
            }),
            c => Err(ParserError::Unexpected {
                unexpected: format!("{:?}", c),
                expected: Some("string".to_owned()),
            }),
        }
    }

    /// Consumes the next token, returning an error if it's not an identifier or
    /// yielding it
    pub(crate) fn expect_identifier(&mut self) -> Result<String, ParserError> {
        match self.peek(0)? {
            Some(&Token::Identifier(ref s)) => {
                let s2 = s.clone();
                self.advance(1);
                Ok(s2)
            }
            None => Err(ParserError::EndOfStream {
                expected: Some("identifier".to_owned()),
            }),
            c => Err(ParserError::Unexpected {
                unexpected: format!("{:?}", c),
                expected: Some("identifier".to_owned()),
            }),
        }
    }

    /// Consumes the next token, returning an error if it does not match the
    /// given token
    pub(crate) fn expect_next(&mut self, token: Token) -> Result<(), ParserError> {
        match self.peek(0)? {
            Some(c) if *c == token => {
                self.advance(1);
                Ok(())
            }
            None => Err(ParserError::EndOfStream {
                expected: Some(format!("{:?}", token)),
            }),
            c => Err(ParserError::Unexpected {
                unexpected: format!("{:?}", c),
                expected: Some(format!("{:?}", token)),
            }),
        }
    }

    /// Skips tokens belonging to [0, n)
    pub(crate) fn advance(&mut self, n: usize) {
        assert!(
            n <= self.tokens.len(),
            "cannot advance over un-peeked tokens"
        );
        self.tokens.drain(0..n);
    }

    /// Peeks (n+1)-tokens ahead, and returns the n-th token if possible
    pub(crate) fn peek(&mut self, n: usize) -> Result<Option<&Token>, ParserError> {
        while self.tokens.len() <= n {
            let token = self.lexer.next().map_err(ParserError::LexerError)?;
            if token != Token::None {
                self.tokens.push(token);
            } else {
                break;
            }
        }

        Ok(self.tokens.get(n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expect_string() {
        let mut s: &[u8] = b"'string'";
        let mut parser = Parser::new(&mut s);
        assert_eq!(parser.expect_string().unwrap(), "string".to_owned());
    }

    #[test]
    fn expect_identifier() {
        let mut s: &[u8] = b"foo";
        let mut parser = Parser::new(&mut s);
        assert_eq!(parser.expect_identifier().unwrap(), "foo".to_owned());
    }

    #[test]
    fn exceed_recursion_limit() {
        let mut s: &[u8] = b"foo";
        let mut parser = Parser::new(&mut s);

        // 500 is enough larger than MAX_RECURSION
        let guards = (0..500)
            .map(|_| parser.get_recursion_guard())
            .collect::<Vec<_>>();
        assert_eq!(guards.last(), Some(&Err(ParserError::RecursionLimit)));
    }
}
