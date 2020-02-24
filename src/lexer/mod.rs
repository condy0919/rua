use std::char;

pub mod lexer;
pub use lexer::*;

pub mod string;
pub use string::*;

pub(crate) fn from_u8(c: u8) -> char {
    char::from_u32(c as u32).unwrap_or(char::REPLACEMENT_CHARACTER)
}

pub(crate) fn from_u16(c: u16) -> char {
    char::from_u32(c as u32).unwrap_or(char::REPLACEMENT_CHARACTER)
}
