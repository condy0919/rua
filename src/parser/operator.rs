use crate::lexer::Token;

/// The precedence lower than any other operators
pub const MIN_OPERATOR_PRECEDENCE: u8 = 0;

/// Binary operator
///
/// The precedence table:
///
/// ```plain
/// | operator        | precedence | associativity |
/// |-----------------|------------|---------------|
/// | ^               | 12         | right         |
/// | * / // %        | 10         | left          |
/// | + -             | 9          | left          |
/// | ..              | 8          | right         |
/// | << >>           | 7          | left          |
/// | &               | 6          | left          |
/// | ~               | 5          | left          |
/// | |               | 4          | left          |
/// | == ~= < <= > >= | 3          | left          |
/// | and             | 2          | left          |
/// | or              | 1          | left          |
/// ```
///
/// # Reference
///
/// https://www.lua.org/manual/5.3/manual.html#3.4.8
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Power,
    Concat,
    And,
    Or,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Equal,
    NotEqual,
    BitXor,
    BitAnd,
    BitOr,
    ShiftLeft,
    ShiftRight,
}

impl Precedence for BinaryOperator {
    fn precedence(&self) -> (u8, Associativity) {
        use BinaryOperator::*;

        match *self {
            Or => (1, Associativity::L),
            And => (2, Associativity::L),
            Equal | NotEqual | LessThan | LessEqual | GreaterThan | GreaterEqual => {
                (3, Associativity::L)
            }
            BitOr => (4, Associativity::L),
            BitXor => (5, Associativity::L),
            BitAnd => (6, Associativity::L),
            ShiftLeft | ShiftRight => (7, Associativity::L),
            Concat => (8, Associativity::R),
            Add | Sub => (9, Associativity::L),
            Mul | Div | IDiv | Mod => (10, Associativity::L),
            // NOTE All unary operators => 11
            Power => (12, Associativity::R),
        }
    }
}

/// Gets the binary operator associated with the given token, if it exists.
pub fn get_binary_operator(token: &Token) -> Option<BinaryOperator> {
    match *token {
        Token::Add => Some(BinaryOperator::Add),
        Token::Minus => Some(BinaryOperator::Sub),
        Token::Mul => Some(BinaryOperator::Mul),
        Token::Div => Some(BinaryOperator::Div),
        Token::IDiv => Some(BinaryOperator::IDiv),
        Token::Mod => Some(BinaryOperator::Mod),
        Token::Power => Some(BinaryOperator::Power),
        Token::Concat => Some(BinaryOperator::Concat),
        Token::And => Some(BinaryOperator::And),
        Token::Or => Some(BinaryOperator::Or),
        Token::LessThan => Some(BinaryOperator::LessThan),
        Token::LessEqual => Some(BinaryOperator::LessEqual),
        Token::GreaterThan => Some(BinaryOperator::GreaterThan),
        Token::GreaterEqual => Some(BinaryOperator::GreaterEqual),
        Token::Equal => Some(BinaryOperator::Equal),
        Token::NotEqual => Some(BinaryOperator::NotEqual),
        Token::BitXorNot => Some(BinaryOperator::BitXor),
        Token::BitAnd => Some(BinaryOperator::BitAnd),
        Token::BitOr => Some(BinaryOperator::BitOr),
        Token::ShiftLeft => Some(BinaryOperator::ShiftLeft),
        Token::ShiftRight => Some(BinaryOperator::ShiftRight),
        _ => None,
    }
}

/// Unary operator
///
/// The precedence table:
///
/// ```plain
/// | operator  | precedence | associativity |
/// |-----------|------------|---------------|
/// | not - ~ # | 11         | non           |
/// ```
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnaryOperator {
    Not,
    Minus,
    BitNot,
    Len,
}

impl Precedence for UnaryOperator {
    fn precedence(&self) -> (u8, Associativity) {
        (11, Associativity::Non)
    }
}

/// Gets the unary operator associated with the given token, if it exists.
pub fn get_unary_operator(token: &Token) -> Option<UnaryOperator> {
    match *token {
        Token::Not => Some(UnaryOperator::Not),
        Token::Minus => Some(UnaryOperator::Minus),
        Token::BitXorNot => Some(UnaryOperator::BitNot),
        Token::Len => Some(UnaryOperator::Len),
        _ => None,
    }
}

/// Operator associativity
///
/// Associativity is only needed when the operators in an expression have the
/// same precedence.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Associativity {
    /// Non-associative
    Non,
    /// Left-associative
    L,
    /// Right-associative
    R,
}

pub trait Precedence {
    fn precedence(&self) -> (u8, Associativity);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;

    #[test]
    fn binary_operator_precedence() {
        macro_rules! lexer_check_next_binary_operator {
            ($lexer:expr, $o:ident, $precedence:expr, $assoc:ident) => {
                let op = get_binary_operator(&$lexer.next().unwrap()).unwrap();
                assert_eq!(op, BinaryOperator::$o);
                assert_eq!(op.precedence().0, $precedence);
                assert_eq!(op.precedence().1, Associativity::$assoc);
            };
        }

        let mut s: &[u8] = b"^ * / // % + - .. << >> & ~ | == ~= < <= > >= and or";
        let mut lexer = Lexer::new(&mut s);

        lexer_check_next_binary_operator!(lexer, Power, 12, R);
        lexer_check_next_binary_operator!(lexer, Mul, 10, L);
        lexer_check_next_binary_operator!(lexer, Div, 10, L);
        lexer_check_next_binary_operator!(lexer, IDiv, 10, L);
        lexer_check_next_binary_operator!(lexer, Mod, 10, L);
        lexer_check_next_binary_operator!(lexer, Add, 9, L);
        lexer_check_next_binary_operator!(lexer, Sub, 9, L);
        lexer_check_next_binary_operator!(lexer, Concat, 8, R);
        lexer_check_next_binary_operator!(lexer, ShiftLeft, 7, L);
        lexer_check_next_binary_operator!(lexer, ShiftRight, 7, L);
        lexer_check_next_binary_operator!(lexer, BitAnd, 6, L);
        lexer_check_next_binary_operator!(lexer, BitXor, 5, L);
        lexer_check_next_binary_operator!(lexer, BitOr, 4, L);
        lexer_check_next_binary_operator!(lexer, Equal, 3, L);
        lexer_check_next_binary_operator!(lexer, NotEqual, 3, L);
        lexer_check_next_binary_operator!(lexer, LessThan, 3, L);
        lexer_check_next_binary_operator!(lexer, LessEqual, 3, L);
        lexer_check_next_binary_operator!(lexer, GreaterThan, 3, L);
        lexer_check_next_binary_operator!(lexer, GreaterEqual, 3, L);
        lexer_check_next_binary_operator!(lexer, And, 2, L);
        lexer_check_next_binary_operator!(lexer, Or, 1, L);
    }

    #[test]
    fn unary_operator_precedence() {
        macro_rules! lexer_check_next_unary_operator {
            ($lexer:expr, $o:ident, $precedence:expr, $assoc:ident) => {
                let op = get_unary_operator(&$lexer.next().unwrap()).unwrap();
                assert_eq!(op, UnaryOperator::$o);
                assert_eq!(op.precedence().0, $precedence);
                assert_eq!(op.precedence().1, Associativity::$assoc);
            };
        }

        let mut s: &[u8] = b"not - ~ #";
        let mut lexer = Lexer::new(&mut s);

        lexer_check_next_unary_operator!(lexer, Not, 11, Non);
        lexer_check_next_unary_operator!(lexer, Minus, 11, Non);
        lexer_check_next_unary_operator!(lexer, BitNot, 11, Non);
        lexer_check_next_unary_operator!(lexer, Len, 11, Non);
    }

    #[test]
    fn get_binary_operator_failed() {
        let token = Token::Assign;
        assert_eq!(get_binary_operator(&token), None);
    }

    #[test]
    fn get_unary_operator_failed() {
        let token = Token::Concat;
        assert_eq!(get_unary_operator(&token), None);
    }
}
