use std::f64;
use std::io;

use super::{ascii_to_digit, ascii_to_hexdigit};
use super::{Lexer, LexerError, Token};

impl<'a, S: io::Read> Lexer<'a, S> {
    /// Reads a hexdecimal/decimal integer or floating point number. Allows
    /// decimal integers (123), hex integers (0xc0debabe), decimal floating
    /// point with optional exponent and exponent sign (3.21e+1), and hex floats
    /// with optional exponent and exponent sign (0xe.2fp-1c).
    pub(crate) fn read_numeral(&mut self) -> Result<Token, LexerError> {
        let p0 = self.peek(0)?.unwrap();
        assert!(p0 == b'.' || p0.is_ascii_digit());

        let p1 = self.peek(1)?;
        let is_hex = p0 == b'0' && (p1 == Some(b'x') || p1 == Some(b'X'));

        let base: f64;
        let conv_fn: fn(u8) -> Option<u8>;
        let expo_sym: [u8; 2];
        if is_hex {
            base = 16.0;
            conv_fn = ascii_to_hexdigit;
            expo_sym = [b'p', b'P'];
            self.advance(2);
        } else {
            base = 10.0;
            conv_fn = ascii_to_digit;
            expo_sym = [b'e', b'E'];
        }

        let mut has_dot = 0;
        let mut digits_after_dot = 0;
        let mut result = 0.0;
        while let Some(c) = self.peek(0)? {
            if c == b'.' {
                has_dot += 1;
                // malformed 1..2
                if has_dot > 1 {
                    return Err(LexerError::BadNumber);
                }
            } else if let Some(d) = conv_fn(c) {
                result = result * base + f64::from(d);
                digits_after_dot += has_dot;
            } else {
                break;
            }

            self.advance(1);
        }

        let mut has_expo = false;
        if let Some(c) = self.peek(0)? {
            if c == expo_sym[0] || c == expo_sym[1] {
                has_expo = true;
                self.advance(1);
            } else if c.is_ascii_alphabetic() || c == b'_' {
                // malformed 1.5p10 1.5_10
                return Err(LexerError::BadNumber);
            }
        }

        if has_expo {
            // Determine the sign of exponent part
            let mut negative = false;
            let c = self.peek(0)?.ok_or(LexerError::BadNumber)?;
            if c == b'+' || c == b'-' {
                self.advance(1);
                if c == b'-' {
                    negative = true;
                }
            }

            let mut expo = 0u32;
            while let Some(c) = self.peek(0)? {
                if let Some(d) = ascii_to_digit(c) {
                    expo = 10 * expo + u32::from(d);
                    self.advance(1);
                } else if c.is_ascii_alphabetic() || c == b'_' {
                    // malformed 2.33e10f
                    return Err(LexerError::BadNumber);
                } else {
                    break;
                }
            }

            let b: i32 = if is_hex { 2 } else { 10 };
            if negative {
                result /= f64::from(b.pow(expo));
            } else {
                result *= f64::from(b.pow(expo));
            }
        }

        result /= base.powi(digits_after_dot);
        if has_expo || has_dot == 1 {
            Ok(Token::Number(result))
        } else {
            Ok(Token::Integer(result as i64))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn float_equal(t: Token, f: f64) -> bool {
        match t {
            Token::Number(n) => (n - f).abs() < f64::EPSILON,
            _ => false,
        }
    }

    #[test]
    fn decimal_integers() {
        let mut s: &[u8] = b"12345 114514";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::Integer(12345));
        assert_eq!(lex.next().unwrap(), Token::Integer(114514));
    }

    #[test]
    fn decimal_floats() {
        let mut s: &[u8] = b"1.5 .5";
        let mut lex = Lexer::new(&mut s);
        assert!(float_equal(lex.next().unwrap(), 1.5));
        assert!(float_equal(lex.next().unwrap(), 0.5));

        let mut s: &[u8] = b"9.9e-2 8.8e3 7.065e+1";
        let mut lex = Lexer::new(&mut s);
        assert!(float_equal(lex.next().unwrap(), 0.099));
        assert!(float_equal(lex.next().unwrap(), 8800.0));
        assert!(float_equal(lex.next().unwrap(), 70.65));
    }

    #[test]
    fn hexadecimal_integers() {
        let mut s: &[u8] = b"0xffff 0XffFF";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap(), Token::Integer(0xffff));
        assert_eq!(lex.next().unwrap(), Token::Integer(0xffff));
    }

    #[test]
    fn hexadecimal_floats() {
        let mut s: &[u8] = b"0xf.5p2";
        let mut lex = Lexer::new(&mut s);
        assert!(float_equal(lex.next().unwrap(), 61.25));
    }

    #[test]
    fn malformed_numbers() {
        let mut s: &[u8] = b"1..2";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::BadNumber);

        let mut s: &[u8] = b"1.5p10";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::BadNumber);

        let mut s: &[u8] = b"1.5_10";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::BadNumber);

        let mut s: &[u8] = b"2.33e10f";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::BadNumber);
    }
}
