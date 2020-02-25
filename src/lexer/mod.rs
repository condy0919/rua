use std::char;

pub mod lexer;
pub use lexer::*;

pub mod string;
pub use string::*;

pub mod number;
pub use number::*;

pub(crate) fn from_u8(c: u8) -> char {
    char::from_u32(c as u32).unwrap_or(char::REPLACEMENT_CHARACTER)
}

pub(crate) fn from_u16(c: u16) -> char {
    char::from_u32(c as u32).unwrap_or(char::REPLACEMENT_CHARACTER)
}

pub(crate) fn ascii_to_hexdigit(c: u8) -> Option<u8> {
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

pub(crate) fn ascii_to_digit(c: u8) -> Option<u8> {
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
