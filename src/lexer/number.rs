use std::io;

use super::{ascii_to_digit, ascii_to_hexdigit};
use super::{Lexer, LexerError, Token};

impl<'a, S: io::Read> Lexer<'a, S> {
    /// Reads a hexdecimal/decimal integer or floating point number. Allows
    /// decimal integers (123), hex integers (0xc0debabe), decimal floating
    /// point with optional exponent and exponent sign (3.21e+1), and hex floats
    /// with optional exponent and exponent sign (0xe.2fp-1c).
    pub(crate) fn read_numeral(&mut self) -> Result<Token, LexerError> {
        // TODO floating points
        let mut is_hex = false;

        let p1 = self.peek(0).unwrap().unwrap();
        let p2 = self.peek(1)?;
        if p1 == b'0' && (p2 == Some(b'x') || p2 == Some(b'X')) {
            is_hex = true;
            self.advance(2);
        }

        let mut value: i64 = 0;
        if is_hex {
            while let Some(c) = self.peek(0)? {
                if let Some(d) = ascii_to_hexdigit(c) {
                    value = value * 16 + d as i64;
                } else {
                    break;
                }
                self.advance(1);
            }
        } else {
            while let Some(c) = self.peek(0)? {
                if let Some(d) = ascii_to_digit(c) {
                    value = value * 10 + d as i64;
                } else {
                    break;
                }
                self.advance(1);
            }
        }

        Ok(Token::Integer(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_integers() {
        let mut s: &[u8] = b"12345";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::Integer(12345));
    }

    #[test]
    fn hexadecimal_integers() {
        let mut s: &[u8] = b"0xffff 0XffFF";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::Integer(0xffff));
        assert_eq!(lex.next().unwrap(), Token::Integer(0xffff));
    }
}
