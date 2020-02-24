use std::char;
use std::io;

use super::{from_u16, from_u8};
use super::{Lexer, LexerError, Token};

impl<'a, S: io::Read> Lexer<'a, S> {
    /// Reads a [=*[...]=*] sequence with matching numbers of '='.
    ///
    /// A long string literal starts with an opening long bracket of any level
    /// and ends at the first closing long bracket of the same level. Literals
    /// in this bracketed form can run for several lines, do not interpret any
    /// escape sequences, and ignore long brackets of any other level.
    pub(crate) fn read_long_string(&mut self) -> Result<Option<Token>, LexerError> {
        assert_eq!(self.peek(0).unwrap().unwrap(), b'[');
        self.advance(1);

        let mut string_buf = String::new();
        let mut open_sep_length = 0;
        while self.peek(0)? == Some(b'=') {
            self.advance(1);
            open_sep_length += 1;
        }

        if self.peek(0)? != Some(b'[') {
            return Err(LexerError::InvalidLongStringDelimiter);
        }
        self.advance(1);

        loop {
            let c = if let Some(c) = self.peek(0)? {
                c
            } else {
                return Err(LexerError::UnfinishedLongString);
            };

            match c {
                b'\r' | b'\n' => {
                    self.add_new_line()?;
                    string_buf.push('\n');
                }

                b']' => {
                    let mut close_sep_length = 0;
                    self.advance(1);
                    while self.peek(0)? == Some(b'=') {
                        self.advance(1);
                        close_sep_length += 1;
                    }

                    if open_sep_length == close_sep_length && self.peek(0)? == Some(b']') {
                        self.advance(1);
                        break;
                    } else {
                        string_buf.push(']');
                        for _ in 0..close_sep_length {
                            string_buf.push('=');
                        }
                    }
                }

                c => {
                    string_buf.push(from_u8(c));
                    self.advance(1);
                }
            }
        }

        Ok(Some(Token::String(string_buf)))
    }

    /// Reads a string on a single line delimited by ' or " that allows for \
    /// escaping of certain characters.
    ///
    /// A short literal string can be delimited by matching single or double
    /// quotes, and can contain the following C-like escape sequences:
    ///
    /// - '\a' (bell)
    /// - '\b' (backspace)
    /// - '\f' (form feed)
    /// - '\n' (newline)
    /// - '\r' (carriage return)
    /// - '\t' (horizontal tab)
    /// - '\v' (vertical tab)
    /// - '\\' (backslash)
    /// - '\"' (quotation mark [double quote])
    /// - '\'' (apostrophe [single quote])
    ///
    /// A backslash followed by a line break results in a newline in the string.
    /// The escape sequence '\z' skips the following span of white-space
    /// characters, including line breaks; it is particularly useful to break
    /// and indent a long literal string into multiple lines without adding the
    /// newlines and spaces into the string contents. A short literal string
    /// cannot contain unescaped line breaks nor escapes not forming a valid
    /// escape sequence. We can specify any byte in a short literal string by
    /// its numeric value (including embedded zeros). This can be done with the
    /// escape sequence \xXX, where XX is a sequence of exactly two hexadecimal
    /// digits, or with the escape sequence \ddd, where ddd is a sequence of up
    /// to three decimal digits.
    ///
    /// The UTF-8 encoding of a Unicode character can be inserted in a literal
    /// string with the escape sequence \u{XXX} (note the mandatory enclosing
    /// brackets), where XXX is a sequence of one or more hexadecimal digits
    /// representing the character code point.
    pub(crate) fn read_short_string(&mut self) -> Result<Option<Token>, LexerError> {
        let start_quote = self.peek(0).unwrap().unwrap();
        assert!(start_quote == b'\'' || start_quote == b'\"');
        self.advance(1);

        let mut string_buf = String::new();
        loop {
            let c = if let Some(c) = self.peek(0)? {
                c
            } else {
                return Err(LexerError::UnfinishedShortString(start_quote));
            };

            if c == b'\r' || c == b'\n' {
                return Err(LexerError::UnfinishedShortString(start_quote));
            }

            self.advance(1);
            if c == b'\\' {
                match self
                    .peek(0)?
                    .ok_or_else(|| LexerError::UnfinishedShortString(start_quote))?
                {
                    b'a' => {
                        self.advance(1);
                        string_buf.push('\x07');
                    }

                    b'b' => {
                        self.advance(1);
                        string_buf.push('\x08');
                    }

                    b'f' => {
                        self.advance(1);
                        string_buf.push('\x0c');
                    }

                    b'n' => {
                        self.advance(1);
                        string_buf.push('\n');
                    }

                    b'r' => {
                        self.advance(1);
                        string_buf.push('\r');
                    }

                    b't' => {
                        self.advance(1);
                        string_buf.push('\t');
                    }

                    b'v' => {
                        self.advance(1);
                        string_buf.push('\x0b');
                    }

                    b'\\' => {
                        self.advance(1);
                        string_buf.push('\\');
                    }

                    b'\'' => {
                        self.advance(1);
                        string_buf.push('\'');
                    }

                    b'\"' => {
                        self.advance(1);
                        string_buf.push('\"');
                    }

                    b'\r' | b'\n' => {
                        self.add_new_line()?;
                        string_buf.push('\n');
                    }

                    // hexadecimal escape sequence, e.g. \x1f
                    b'x' => {
                        self.advance(1);
                        let first = self
                            .peek(0)?
                            .and_then(ascii_to_hexdigit)
                            .ok_or(LexerError::HexDigitExpected)?;
                        let second = self
                            .peek(1)?
                            .and_then(ascii_to_hexdigit)
                            .ok_or(LexerError::HexDigitExpected)?;
                        string_buf.push(from_u8(first << 4 | second));
                        self.advance(2);
                    }

                    // UTF-8 escape sequence, e.g. \u{XXX}
                    // The length of escape sequence must be greater than ZERO.
                    b'u' => {
                        if self.peek(1)? != Some(b'{') {
                            return Err(LexerError::EscapeUnicodeStart);
                        }
                        self.advance(2);

                        let mut seq_len: usize = 0;
                        let mut u: u32 = 0;
                        loop {
                            if let Some(c) = self.peek(0)? {
                                if c == b'}' {
                                    self.advance(1);
                                    break;
                                } else if let Some(h) = ascii_to_hexdigit(c) {
                                    u = (u << 4) | h as u32;
                                    seq_len += 1;
                                    self.advance(1);
                                } else {
                                    return Err(LexerError::EscapeUnicodeEnd);
                                }
                            } else {
                                return Err(LexerError::EscapeUnicodeEnd);
                            }
                        }

                        if seq_len == 0 {
                            return Err(LexerError::EscapeUnicodeInvalid);
                        }

                        let c = char::from_u32(u).ok_or(LexerError::EscapeUnicodeInvalid)?;
                        string_buf.push(c);
                    }

                    // The escape sequence '\z' skips the following span of
                    // white-space characters, including line breaks.
                    b'z' => {
                        self.advance(1);
                        while let Some(c) = self.peek(0)? {
                            if c == b'\r' || c == b'\n' {
                                self.add_new_line()?;
                            } else if c.is_ascii_whitespace() {
                                self.advance(1);
                            } else {
                                break;
                            }
                        }
                    }

                    // the escape sequence \ddd, where ddd is a sequence of up
                    // to three decimal digits.
                    c if c.is_ascii_digit() => {
                        let mut u: u16 = 0;
                        if let Some(d) = self.peek(0)?.and_then(ascii_to_digit) {
                            u = 10 * u + d as u16;
                            self.advance(1);
                        } else {
                            return Err(LexerError::EscapeDecimalInvalid);
                        }

                        if let Some(d) = self.peek(0)?.and_then(ascii_to_digit) {
                            u = 10 * u + d as u16;
                            self.advance(1);
                        }

                        if let Some(d) = self.peek(0)?.and_then(ascii_to_digit) {
                            u = 10 * u + d as u16;
                            self.advance(1);
                        }

                        if u > 255 {
                            return Err(LexerError::EscapeDecimalTooLarge);
                        }
                        string_buf.push(from_u16(u));
                    }

                    _ => return Err(LexerError::InvalidEscape),
                }
            } else if c == start_quote {
                break;
            } else {
                string_buf.push(from_u8(c));
            }
        }

        Ok(Some(Token::String(string_buf)))
    }
}

fn ascii_to_hexdigit(c: u8) -> Option<u8> {
    match c {
        b'0' => Some(0),
        b'1' => Some(1),
        b'2' => Some(2),
        b'3' => Some(3),
        b'4' => Some(4),
        b'5' => Some(5),
        b'6' => Some(6),
        b'7' => Some(7),
        b'8' => Some(8),
        b'9' => Some(9),
        b'a' | b'A' => Some(10),
        b'b' | b'B' => Some(11),
        b'c' | b'C' => Some(12),
        b'd' | b'D' => Some(13),
        b'e' | b'E' => Some(14),
        b'f' | b'F' => Some(15),
        _ => None,
    }
}

fn ascii_to_digit(c: u8) -> Option<u8> {
    match c {
        b'0' => Some(0),
        b'1' => Some(1),
        b'2' => Some(2),
        b'3' => Some(3),
        b'4' => Some(4),
        b'5' => Some(5),
        b'6' => Some(6),
        b'7' => Some(7),
        b'8' => Some(8),
        b'9' => Some(9),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn long_string_invalid_delimiter() {
        let mut s: &[u8] = b"[==invalid==]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap_err(),
            LexerError::InvalidLongStringDelimiter
        );
    }

    #[test]
    fn long_string_unfinished() {
        let mut s: &[u8] = b"[==[unfinished]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::UnfinishedLongString);
    }

    #[test]
    fn long_string_crlf() {
        // \r\n
        let mut s: &[u8] = b"[==[\r\nhere]==]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("\nhere".to_owned())
        );
        assert_eq!(lex.next().unwrap(), None);

        // \n\n
        let mut s: &[u8] = b"[==[\n\ntwo lines]==]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("\n\ntwo lines".to_owned())
        );

        // \r\r
        let mut s: &[u8] = b"[==[\r\rtwo lines]==]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("\n\ntwo lines".to_owned())
        );

        // \n\r
        let mut s: &[u8] = b"[==[\n\rone line]==]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("\none line".to_owned())
        );
    }

    #[test]
    fn long_string_many_brackets() {
        let mut s: &[u8] = b"[===[first line\n]==]]]]\rsecond line\n]===]";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("first line\n]==]]]]\nsecond line\n".to_owned())
        );
    }

    #[test]
    fn short_string_single_quote() {
        let mut s: &[u8] = b"'single quote'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("single quote".to_owned())
        );
    }

    #[test]
    fn short_string_double_quotes() {
        let mut s: &[u8] = b"\"double quotes\"";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("double quotes".to_owned())
        );
    }

    #[test]
    fn short_string_unfinished() {
        let mut s: &[u8] = b"'unfinished1";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap_err(),
            LexerError::UnfinishedShortString(b'\'')
        );

        let mut s: &[u8] = b"'unfinished2\n'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap_err(),
            LexerError::UnfinishedShortString(b'\'')
        );

        let mut s: &[u8] = b"'unfinished3\\'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap_err(),
            LexerError::UnfinishedShortString(b'\'')
        );
    }

    #[test]
    fn short_string_hexdigit_expected() {
        let mut s: &[u8] = b"'no hexdigits \\x'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::HexDigitExpected);

        let mut s: &[u8] = b"'1 hexdigit \\xa'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::HexDigitExpected);

        let mut s: &[u8] = b"'2 hexdigits \\x1f'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("2 hexdigits \x1f".to_owned())
        );

        let mut s: &[u8] = b"'invalid hexdigits \\xxyz'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::HexDigitExpected);
    }

    #[test]
    fn short_string_escape_unicode() {
        let mut s: &[u8] = b"'unicode \\u00c}'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::EscapeUnicodeStart);

        let mut s: &[u8] = b"'unicode \\u{00c'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::EscapeUnicodeEnd);

        let mut s: &[u8] = b"'unicode \\u{00c";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::EscapeUnicodeEnd);

        let mut s: &[u8] = b"'unicode \\u{110000}";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::EscapeUnicodeInvalid);

        let mut s: &[u8] = b"'unicode \\u{}'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::EscapeUnicodeInvalid);

        let mut s: &[u8] = b"'unicode \\u{00c}'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("unicode \x0c".to_owned())
        );

        let mut s: &[u8] = b"'unicode \\u{00c} unicode'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("unicode \x0c unicode".to_owned())
        );
    }

    #[test]
    fn short_string_escape_decimal() {
        let mut s: &[u8] = b"'decimal \\12'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("decimal \x0c".to_owned())
        );

        let mut s: &[u8] = b"'decimal \\9f0'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("decimal \tf0".to_owned())
        );

        let mut s: &[u8] = b"'decimal \\256'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(lex.next().unwrap_err(), LexerError::EscapeDecimalTooLarge);

        let mut s: &[u8] = b"'decimal \\097'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("decimal a".to_owned())
        );
    }

    #[test]
    fn short_string_escape() {
        let mut s: &[u8] = b"'escape \\a \\b \\f \\n \\r \\t \\v \\\\ \\\' \\\"'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("escape \x07 \x08 \x0c \n \r \t \x0b \\ \' \"".to_owned())
        );
    }

    #[test]
    fn short_string_slash_z() {
        let mut s: &[u8] = b"'slash z \\z\n     line1\\z\n\\z\n\n'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("slash z line1".to_owned())
        );
    }

    #[test]
    fn short_string_slash() {
        let mut s: &[u8] = b"'slash \\\nfirst \\\nsecond'";
        let mut lex = Lexer::new(&mut s);
        assert_eq!(
            lex.next().unwrap().unwrap(),
            Token::String("slash \nfirst \nsecond".to_owned())
        );
    }
}
