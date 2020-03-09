use std::f64;
use std::mem;

use super::{BinaryOperator, Expression, ParserError, Suffix, SuffixedExpression, UnaryOperator};

/// Evaluate expression in compile time.
pub fn consteval_expression(expr: Expression) -> Result<Expression, ParserError> {
    match expr {
        Expression::UnaryOperator(..) => consteval_unary_expression(expr),
        Expression::BinaryOperator(..) => consteval_binary_expression(expr),
        _ => Ok(expr),
    }
}

// Evaluate unary arithmetic/bitwise/logical/string operations in compile time.
fn consteval_unary_expression(mut expr: Expression) -> Result<Expression, ParserError> {
    match expr {
        Expression::UnaryOperator(UnaryOperator::Minus, ref mut subexpr) => {
            consteval_arithmetic_check(&subexpr)?;

            match **subexpr {
                // minus minus optimization
                Expression::UnaryOperator(UnaryOperator::Minus, ref mut sub) => {
                    Ok(mem::take(&mut **sub))
                }

                Expression::Integer(i) => Ok(Expression::Integer(-i)),
                Expression::Number(n) => Ok(Expression::Number(-n)),

                // Identifier, FunctionCall, TableFieldAccess or other unary/binary
                // expressions
                _ => Ok(expr),
            }
        }
        Expression::UnaryOperator(UnaryOperator::BitNot, ref mut subexpr) => {
            consteval_bitwise_operation_check(&subexpr)?;

            match **subexpr {
                // bitnot bitnot optimization
                Expression::UnaryOperator(UnaryOperator::BitNot, ref mut sub) => {
                    Ok(mem::take(&mut **sub))
                }

                Expression::Integer(i) => Ok(Expression::Integer(!i)),

                _ => Ok(expr),
            }
        }
        Expression::UnaryOperator(UnaryOperator::Not, ref mut subexpr) => {
            consteval_logical_operation_check(&subexpr)?;

            match **subexpr {
                // not not optimization
                //
                // NOTE
                //
                // ```lua
                // a = nil
                // b = not not a
                // type(b) -- print boolean
                // ```
                //
                // After applying this aggressive optimization, `b` has the `nil`
                // type.
                //
                // This is different from Lua.
                Expression::UnaryOperator(UnaryOperator::Not, ref mut sub) => {
                    Ok(mem::take(&mut **sub))
                }

                Expression::Nil | Expression::False => Ok(Expression::True),
                // Any values different from `nil` and `false` are considered
                // `true`.
                Expression::True
                | Expression::Integer(_)
                | Expression::Number(_)
                | Expression::String(_)
                | Expression::Function(_)
                | Expression::TableConstructor(_) => Ok(Expression::False),

                _ => Ok(expr),
            }
        }
        Expression::UnaryOperator(UnaryOperator::Len, ref subexpr) => {
            consteval_string_operation_check(&subexpr)?;

            match subexpr.as_ref() {
                Expression::String(s) => Ok(Expression::Integer(s.len() as i64)),

                _ => Ok(expr),
            }
        }
        _ => unreachable!(),
    }
}

// Eval binary arithmetic/bitwise/logical/string operations in compile time.
fn consteval_binary_expression(mut expr: Expression) -> Result<Expression, ParserError> {
    match expr {
        Expression::BinaryOperator(op, ref lhs, ref rhs)
            if op == BinaryOperator::Add
                || op == BinaryOperator::Sub
                || op == BinaryOperator::Mul
                || op == BinaryOperator::Div
                || op == BinaryOperator::IDiv
                || op == BinaryOperator::Mod
                || op == BinaryOperator::Power
                || op == BinaryOperator::LessThan
                || op == BinaryOperator::LessEqual
                || op == BinaryOperator::GreaterThan
                || op == BinaryOperator::GreaterEqual =>
        {
            consteval_arithmetic_check(&lhs)?;
            consteval_arithmetic_check(&rhs)?;

            match **lhs {
                Expression::Integer(i1) => match **rhs {
                    Expression::Integer(i2) => ConstEvalArithmetic::eval(op, i1, i2),
                    Expression::Number(n2) => ConstEvalArithmetic::eval(op, i1 as f64, n2),
                    _ => Ok(expr),
                },
                Expression::Number(n1) => match **rhs {
                    Expression::Integer(i2) => ConstEvalArithmetic::eval(op, n1, i2 as f64),
                    Expression::Number(n2) => ConstEvalArithmetic::eval(op, n1, n2),
                    _ => Ok(expr),
                },
                _ => Ok(expr),
            }
        }
        Expression::BinaryOperator(op, ref lhs, ref rhs)
            if op == BinaryOperator::ShiftLeft
                || op == BinaryOperator::ShiftRight
                || op == BinaryOperator::BitAnd
                || op == BinaryOperator::BitOr
                || op == BinaryOperator::BitXor =>
        {
            consteval_bitwise_operation_check(&lhs)?;
            consteval_bitwise_operation_check(&rhs)?;

            match (lhs.as_ref(), rhs.as_ref()) {
                (Expression::Integer(i1), Expression::Integer(i2)) => Ok(match op {
                    BinaryOperator::ShiftLeft => Expression::Integer(i1 << i2),
                    BinaryOperator::ShiftRight => Expression::Integer(i1 >> i2),
                    BinaryOperator::BitAnd => Expression::Integer(i1 & i2),
                    BinaryOperator::BitOr => Expression::Integer(i1 | i2),
                    BinaryOperator::BitXor => Expression::Integer(i1 ^ i2),
                    _ => unreachable!(),
                }),
                _ => Ok(expr),
            }
        }
        Expression::BinaryOperator(BinaryOperator::And, ref lhs, ref mut rhs) => {
            consteval_logical_operation_check(&lhs)?;
            consteval_logical_operation_check(&rhs)?;

            match lhs.as_ref() {
                Expression::Nil | Expression::False => Ok(Expression::False),
                Expression::True
                | Expression::Integer(_)
                | Expression::Number(_)
                | Expression::String(_)
                | Expression::Function(_)
                | Expression::TableConstructor(_) => Ok(mem::take(&mut **rhs)),
                _ => Ok(expr),
            }
        }
        Expression::BinaryOperator(BinaryOperator::Or, ref lhs, ref mut rhs) => {
            consteval_logical_operation_check(&lhs)?;
            consteval_logical_operation_check(&rhs)?;

            match lhs.as_ref() {
                Expression::Nil | Expression::False => Ok(mem::take(&mut **rhs)),
                Expression::True
                | Expression::Integer(_)
                | Expression::Number(_)
                | Expression::String(_)
                | Expression::Function(_)
                | Expression::TableConstructor(_) => Ok(Expression::True),
                _ => Ok(expr),
            }
        }
        Expression::BinaryOperator(op, ref lhs, ref rhs)
            if op == BinaryOperator::Equal || op == BinaryOperator::NotEqual =>
        {
            consteval_logical_operation_check(&lhs)?;
            consteval_logical_operation_check(&rhs)?;

            // See `expression_compare` comments for more information
            let comp_result = expression_compare(&*lhs, &*rhs).map(|b| {
                if op == BinaryOperator::Equal {
                    b
                } else {
                    !b
                }
            });
            match comp_result {
                Some(true) => Ok(Expression::True),
                Some(false) => Ok(Expression::False),
                _ => Ok(expr),
            }
        }
        Expression::BinaryOperator(BinaryOperator::Concat, ref lhs, ref rhs) => {
            consteval_string_operation_check(&lhs)?;
            consteval_string_operation_check(&rhs)?;

            match (lhs.as_ref(), rhs.as_ref()) {
                (Expression::String(s1), Expression::String(s2)) => {
                    Ok(Expression::String(format!("{}{}", s1, s2)))
                }
                _ => Ok(expr),
            }
        }
        _ => unreachable!(),
    }
}

// ```plain
// Unary      ::= Integer | Number | True | False
// Binary     ::= Integer | Number | True | False | String
// Identifier ::= Nil | Integer | Number | True | False | String
// Suffixed   ::= Nil | Integer | Number | True | False | String
// ```
//
// |         | Nil | True | False | Integer | Number | String | Unary | Binary |
// |---------+-----+------+-------+---------+--------+--------+-------+--------|
// | Nil     | o   | x    | x     | x       | x      | x      | x     | x      |
// | True    | x   | o    | x     | x       | x      | x      |       |        |
// | False   | x   | x    | o     | x       | x      | x      |       |        |
// | Integer | x   | x    | x     | check   | check  | x      |       |        |
// | Number  | x   | x    | x     | check   | check  | x      |       |        |
// | String  | x   | x    | x     | x       | x      | check  | x     |        |
// | Unary   | x   |      |       |         |        | x      | check |        |
// | Binary  | x   |      |       |         |        |        |       | check  |
//
// where `o` means `true`, `x` means false, blank means undetermined.
//
// There are three cases here:
//
// 1. `lhs` and `rhs` are comparable, the result is `true`
// 2. `lhs` and `rhs` are comparable with different value or
//   uncomparable, both results are `false`
// 3. It cannot be determined now (lack of information)
//
// We use `Option<true>` to represent the above cases.
fn expression_compare(lhs: &Expression, rhs: &Expression) -> Option<bool> {
    match (lhs, rhs) {
        // The function type and table type are not primitive, only can
        // be comapred by reference.
        (Expression::Function(_), _) | (Expression::TableConstructor(_), _) => Some(false),
        (_, Expression::Function(_)) | (_, Expression::TableConstructor(_)) => Some(false),

        // Identifier
        //
        // a == a must be `true`
        (Expression::Identifier(id1), Expression::Identifier(id2)) if id1 == id2 => Some(true),

        // SuffixedExpression
        (Expression::Suffixed(suffix1), Expression::Suffixed(suffix2))
            if suffixed_expression_compare(suffix1, suffix2) == Some(true) =>
        {
            Some(true)
        }

        // BinaryOperator
        (Expression::Nil, Expression::BinaryOperator(..))
        | (Expression::BinaryOperator(..), Expression::Nil) => Some(false),
        (Expression::BinaryOperator(o1, l1, r1), Expression::BinaryOperator(o2, l2, r2))
            if o1 == o2
                && expression_compare(l1, l2) == Some(true)
                && expression_compare(r1, r2) == Some(true) =>
        {
            Some(true)
        }

        // UnaryOperator
        (Expression::Nil, Expression::UnaryOperator(..))
        | (Expression::UnaryOperator(..), Expression::Nil) => Some(false),
        (Expression::String(..), Expression::UnaryOperator(..))
        | (Expression::UnaryOperator(..), Expression::String(..)) => Some(false),
        (Expression::UnaryOperator(o1, e1), Expression::UnaryOperator(o2, e2))
            if o1 == o2 && expression_compare(e1, e2) == Some(true) =>
        {
            Some(true)
        }

        // String
        (Expression::String(s1), Expression::String(s2)) => Some(s1 == s2),
        (Expression::String(_), Expression::Nil)
        | (Expression::String(_), Expression::True)
        | (Expression::String(_), Expression::False)
        | (Expression::String(_), Expression::Integer(_))
        | (Expression::String(_), Expression::Number(_)) => Some(false),
        (Expression::Nil, Expression::String(_))
        | (Expression::True, Expression::String(_))
        | (Expression::False, Expression::String(_))
        | (Expression::Integer(_), Expression::String(_))
        | (Expression::Number(_), Expression::String(_)) => Some(false),

        // Number/Integer
        (Expression::Integer(i1), Expression::Integer(i2)) => Some(i1 == i2),
        (Expression::Integer(i1), Expression::Number(n2)) => {
            Some(((*i1 as f64) - n2).abs() < f64::EPSILON)
        }
        (Expression::Number(n1), Expression::Integer(i2)) => {
            Some((n1 - (*i2 as f64)).abs() < f64::EPSILON)
        }
        (Expression::Number(n1), Expression::Number(n2)) => Some((n1 - n2).abs() < f64::EPSILON),
        (Expression::Integer(_), Expression::Nil)
        | (Expression::Integer(_), Expression::True)
        | (Expression::Integer(_), Expression::False) => Some(false),
        (Expression::Nil, Expression::Integer(_))
        | (Expression::True, Expression::Integer(_))
        | (Expression::False, Expression::Integer(_)) => Some(false),
        (Expression::Number(_), Expression::Nil)
        | (Expression::Number(_), Expression::True)
        | (Expression::Number(_), Expression::False) => Some(false),
        (Expression::Nil, Expression::Number(_))
        | (Expression::True, Expression::Number(_))
        | (Expression::False, Expression::Number(_)) => Some(false),

        // Nil
        (Expression::Nil, Expression::Nil) => Some(true),
        (Expression::Nil, _) | (_, Expression::Nil) => Some(false),

        // True/False
        (Expression::True, Expression::True) | (Expression::False, Expression::False) => Some(true),
        (Expression::True, Expression::False) | (Expression::False, Expression::True) => {
            Some(false)
        }
        _ => None,
    }
}

// SuffixedExpression
//
// a.b == a.b
// a[e] == a[e]
// a(e) == a(e)
// a:m(e) == a:m(e)
//
// All must be `true`
fn suffixed_expression_compare(lhs: &SuffixedExpression, rhs: &SuffixedExpression) -> Option<bool> {
    if_chain! {
        if expression_compare(&*lhs.primary, &*rhs.primary) == Some(true);
        if lhs.suffixes.len() == rhs.suffixes.len();
        if lhs.suffixes.iter().zip(rhs.suffixes.iter())
            .all(|(s1, s2)| -> bool {
                match (s1, s2) {
                    (Suffix::NamedField(n1), Suffix::NamedField(n2)) => n1 == n2,
                    (Suffix::IndexedField(e1), Suffix::IndexedField(e2)) => {
                        expression_compare(e1, e2) == Some(true)
                    }
                    (Suffix::FunctionCall(xs), Suffix::FunctionCall(ys)) => {
                        xs.iter().zip(ys.iter())
                            .all(|(e1, e2)| expression_compare(e1, e2) == Some(true))
                    }
                    (Suffix::MethodCall(m1, xs), Suffix::MethodCall(m2, ys)) => {
                        m1 == m2
                        && xs.iter().zip(ys.iter())
                            .all(|(e1, e2)| expression_compare(e1, e2) == Some(true))
                    }
                    _ => false,
                }
            });
        then {
            Some(true)
        } else {
            None
        }
    }
}

// Integer promotion supports.
//
// `/` (Div) and `^` (Power) always produce `Number` types.
trait ConstEvalArithmetic<T, U> {
    fn eval(self, lhs: T, rhs: U) -> Result<Expression, ParserError>;
}

impl ConstEvalArithmetic<i64, i64> for BinaryOperator {
    fn eval(self, lhs: i64, rhs: i64) -> Result<Expression, ParserError> {
        Ok(match self {
            BinaryOperator::Add => Expression::Integer(lhs + rhs),
            BinaryOperator::Sub => Expression::Integer(lhs - rhs),
            BinaryOperator::Mul => Expression::Integer(lhs * rhs),
            BinaryOperator::Div => {
                if rhs == 0 {
                    return Err(ParserError::DividedByZero);
                }
                Expression::Number(lhs as f64 / rhs as f64)
            }
            BinaryOperator::IDiv => {
                if rhs == 0 {
                    return Err(ParserError::DividedByZero);
                }
                Expression::Integer(lhs / rhs)
            }
            BinaryOperator::Mod => Expression::Integer(lhs % rhs),
            BinaryOperator::Power => Expression::Number((lhs as f64).powf(rhs as f64)),
            BinaryOperator::LessThan => {
                if lhs < rhs {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            BinaryOperator::LessEqual => {
                if lhs <= rhs {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            BinaryOperator::GreaterThan => {
                if lhs > rhs {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            BinaryOperator::GreaterEqual => {
                if lhs >= rhs {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            _ => unreachable!(),
        })
    }
}

impl ConstEvalArithmetic<f64, f64> for BinaryOperator {
    fn eval(self, lhs: f64, rhs: f64) -> Result<Expression, ParserError> {
        Ok(match self {
            BinaryOperator::Add => Expression::Number(lhs + rhs),
            BinaryOperator::Sub => Expression::Number(lhs - rhs),
            BinaryOperator::Mul => Expression::Number(lhs * rhs),
            BinaryOperator::Div => Expression::Number(lhs / rhs),
            BinaryOperator::IDiv => Expression::Number((lhs / rhs).floor()),
            BinaryOperator::Mod => Expression::Number(lhs % rhs),
            BinaryOperator::Power => Expression::Number(lhs.powf(rhs)),
            BinaryOperator::LessThan => {
                if lhs < rhs {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            BinaryOperator::LessEqual => {
                if lhs < rhs || (lhs - rhs).abs() < f64::EPSILON {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            BinaryOperator::GreaterThan => {
                if lhs > rhs {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            BinaryOperator::GreaterEqual => {
                if lhs > rhs || (lhs - rhs).abs() < f64::EPSILON {
                    Expression::True
                } else {
                    Expression::False
                }
            }
            _ => unreachable!(),
        })
    }
}

// Perform arithmetic check. Only `Integer` and `Number` types are allowed.
fn consteval_arithmetic_check(expr: &Expression) -> Result<(), ParserError> {
    match expr {
        Expression::Nil => Err(ParserError::Unexpected {
            unexpected: "nil value".to_string(),
            expected: None,
        }),
        Expression::True | Expression::False => Err(ParserError::Unexpected {
            unexpected: "boolean value".to_string(),
            expected: None,
        }),
        // Convertion from **String** to **Numeric** is insane.
        //
        // NOTE Incompatible with Lua 5.3
        Expression::String(_) => Err(ParserError::Unexpected {
            unexpected: "string value".to_string(),
            expected: None,
        }),
        Expression::Dots => Err(ParserError::Unexpected {
            unexpected: "'...'".to_string(),
            expected: None,
        }),
        Expression::Function(_) => Err(ParserError::Unexpected {
            unexpected: "function value".to_string(),
            expected: None,
        }),
        Expression::TableConstructor(_) => Err(ParserError::Unexpected {
            unexpected: "table value".to_string(),
            expected: None,
        }),
        _ => Ok(()),
    }
}

// Perform bitwise operation check. Only `Integer` types are allowed.
fn consteval_bitwise_operation_check(expr: &Expression) -> Result<(), ParserError> {
    match expr {
        Expression::Nil => Err(ParserError::Unexpected {
            unexpected: "nil value".to_string(),
            expected: None,
        }),
        Expression::True | Expression::False => Err(ParserError::Unexpected {
            unexpected: "boolean value".to_string(),
            expected: None,
        }),
        // ```lua
        // ~1.0
        // ```
        //
        // prints `-2`
        //
        // NOTE Incompatible with Lua 5.3
        Expression::Number(_) => Err(ParserError::Unexpected {
            unexpected: "float value".to_string(),
            expected: None,
        }),
        Expression::String(_) => Err(ParserError::Unexpected {
            unexpected: "string value".to_string(),
            expected: None,
        }),
        Expression::Dots => Err(ParserError::Unexpected {
            unexpected: "'...'".to_string(),
            expected: None,
        }),
        Expression::Function(_) => Err(ParserError::Unexpected {
            unexpected: "function value".to_string(),
            expected: None,
        }),
        Expression::TableConstructor(_) => Err(ParserError::Unexpected {
            unexpected: "table value".to_string(),
            expected: None,
        }),
        _ => Ok(()),
    }
}

// Perform logical operation type check.
//
// See `consteval_unary_expression` for more information.
fn consteval_logical_operation_check(expr: &Expression) -> Result<(), ParserError> {
    match expr {
        // ```lua
        // not ...
        // ```
        //
        // Lua repl prints `true`.
        //
        // NOTE Incompatible with Lua 5.3
        Expression::Dots => Err(ParserError::Unexpected {
            unexpected: "'...'".to_string(),
            expected: None,
        }),
        _ => Ok(()),
    }
}

// Perform string operation type check. Only `String` types are allowed.
fn consteval_string_operation_check(expr: &Expression) -> Result<(), ParserError> {
    match expr {
        Expression::Nil => Err(ParserError::Unexpected {
            unexpected: "nil value".to_string(),
            expected: None,
        }),
        Expression::True | Expression::False => Err(ParserError::Unexpected {
            unexpected: "boolean value".to_string(),
            expected: None,
        }),
        // ```lua
        // 'string' .. 1
        // ```
        //
        // will result `'string1'`
        //
        // NOTE Incompatible with Lua 5.3
        Expression::Integer(_) | Expression::Number(_) => Err(ParserError::Unexpected {
            unexpected: "number value".to_string(),
            expected: None,
        }),
        Expression::Dots => Err(ParserError::Unexpected {
            unexpected: "'...'".to_string(),
            expected: None,
        }),
        Expression::Function(_) => Err(ParserError::Unexpected {
            unexpected: "function value".to_string(),
            expected: None,
        }),
        Expression::TableConstructor(_) => Err(ParserError::Unexpected {
            unexpected: "table value".to_string(),
            expected: None,
        }),
        Expression::UnaryOperator(_, _) => Err(ParserError::Unexpected {
            unexpected: "prefixed with an unary operator expression".to_string(),
            expected: None,
        }),
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{Block, FunctionDefinition, TableConstructor};

    macro_rules! id {
        ($name:expr) => {
            Expression::Identifier($name.to_owned())
        };
    }

    const NOP_FUNCTION: Expression = Expression::Function(FunctionDefinition {
        parameters: Vec::new(),
        has_varargs: false,
        body: Block {
            stmts: Vec::new(),
            retstmt: None,
        },
    });

    const NOP_TABLE: Expression =
        Expression::TableConstructor(TableConstructor { fields: Vec::new() });

    #[test]
    fn unary_minus_consteval() {
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Minus,
                Box::new(Expression::Integer(10))
            ))
            .unwrap(),
            Expression::Integer(-10)
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Minus,
                Box::new(Expression::Number(0.0))
            ))
            .unwrap(),
            Expression::Number(0.0)
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Minus,
                Box::new(Expression::UnaryOperator(
                    UnaryOperator::Minus,
                    Box::new(Expression::Integer(42))
                ))
            ))
            .unwrap(),
            Expression::Integer(42)
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Minus,
                Box::new(Expression::UnaryOperator(
                    UnaryOperator::Minus,
                    Box::new(id!("a"))
                ))
            ))
            .unwrap(),
            id!("a")
        );
    }

    #[test]
    fn unary_bitnot_consteval() {
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::BitNot,
                Box::new(Expression::Integer(10))
            ))
            .unwrap(),
            Expression::Integer(-11)
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::BitNot,
                Box::new(Expression::UnaryOperator(
                    UnaryOperator::BitNot,
                    Box::new(id!("a"))
                ))
            ))
            .unwrap(),
            id!("a")
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::BitNot,
                Box::new(id!("a"))
            ))
            .unwrap(),
            Expression::UnaryOperator(UnaryOperator::BitNot, Box::new(id!("a")))
        );
    }

    #[test]
    fn unary_not_consteval() {
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::Nil)
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::False)
            ))
            .unwrap(),
            Expression::True
        );

        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::True)
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::Integer(0))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::Number(1.0))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::String("foo".to_owned()))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(NOP_FUNCTION)
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(NOP_TABLE)
            ))
            .unwrap(),
            Expression::False
        );

        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::UnaryOperator(
                    UnaryOperator::Not,
                    Box::new(id!("a"))
                ))
            ))
            .unwrap(),
            id!("a")
        );
    }

    #[test]
    fn unary_string_get_length_consteval() {
        assert_eq!(
            consteval_expression(Expression::UnaryOperator(
                UnaryOperator::Len,
                Box::new(Expression::String("foo".to_owned()))
            ))
            .unwrap(),
            Expression::Integer(3)
        );
    }

    #[test]
    fn binary_arithmetic_consteval() {
        // arithmetic for Integer
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Add,
                Box::new(Expression::Integer(10)),
                Box::new(Expression::Integer(200))
            ))
            .unwrap(),
            Expression::Integer(210)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Add,
                Box::new(Expression::Integer(10)),
                Box::new(Expression::Number(300.0))
            ))
            .unwrap(),
            Expression::Number(310.0)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Mul,
                Box::new(Expression::Integer(10)),
                Box::new(Expression::Number(-0.5))
            ))
            .unwrap(),
            Expression::Number(-5.0)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Div,
                Box::new(Expression::Integer(4)),
                Box::new(Expression::Integer(1))
            ))
            .unwrap(),
            Expression::Number(4.0)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::IDiv,
                Box::new(Expression::Integer(6)),
                Box::new(Expression::Integer(5))
            ))
            .unwrap(),
            Expression::Integer(1)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Power,
                Box::new(Expression::Integer(2)),
                Box::new(Expression::Integer(10))
            ))
            .unwrap(),
            Expression::Number(1024.0)
        );

        // < <= > >= for Integer
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::LessThan,
                Box::new(Expression::Integer(10)),
                Box::new(Expression::Integer(100))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::LessEqual,
                Box::new(Expression::Integer(100)),
                Box::new(Expression::Integer(10))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::GreaterThan,
                Box::new(Expression::Integer(4)),
                Box::new(Expression::Integer(3))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::GreaterEqual,
                Box::new(Expression::Integer(1)),
                Box::new(Expression::Integer(3))
            ))
            .unwrap(),
            Expression::False
        );

        // < <= > >= for Integer/Number
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::LessThan,
                Box::new(Expression::Number(10.0)),
                Box::new(Expression::Integer(1))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::LessEqual,
                Box::new(Expression::Integer(1)),
                Box::new(Expression::Number(0.5))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::GreaterThan,
                Box::new(Expression::Number(99.1)),
                Box::new(Expression::Integer(99))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::GreaterEqual,
                Box::new(Expression::Number(99.999)),
                Box::new(Expression::Integer(100))
            ))
            .unwrap(),
            Expression::False
        );
    }

    #[test]
    fn binary_bitwise_operation_consteval() {
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::ShiftLeft,
                Box::new(Expression::Integer(5)),
                Box::new(Expression::Integer(1))
            ))
            .unwrap(),
            Expression::Integer(5 << 1)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::ShiftRight,
                Box::new(Expression::Integer(11)),
                Box::new(Expression::Integer(2))
            ))
            .unwrap(),
            Expression::Integer(2)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::BitAnd,
                Box::new(Expression::Integer(0xaa)),
                Box::new(Expression::Integer(0x33))
            ))
            .unwrap(),
            Expression::Integer(0xaa & 0x33)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::BitOr,
                Box::new(Expression::Integer(0xaa)),
                Box::new(Expression::Integer(0x33))
            ))
            .unwrap(),
            Expression::Integer(0xaa | 0x33)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::BitXor,
                Box::new(Expression::Integer(0xaa)),
                Box::new(Expression::Integer(0x33))
            ))
            .unwrap(),
            Expression::Integer(0xaa ^ 0x33)
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::BitAnd,
                Box::new(Expression::Integer(10)),
                Box::new(id!("a"))
            ))
            .unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::BitAnd,
                Box::new(Expression::Integer(10)),
                Box::new(id!("a"))
            )
        );
    }

    #[test]
    fn binary_logical_operation_consteval() {
        // and
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::And,
                Box::new(Expression::Nil),
                Box::new(id!("a"))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::And,
                Box::new(Expression::True),
                Box::new(Expression::String("foo".to_owned()))
            ))
            .unwrap(),
            Expression::String("foo".to_owned())
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::And,
                Box::new(NOP_TABLE),
                Box::new(id!("a"))
            ))
            .unwrap(),
            id!("a")
        );

        // or
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Or,
                Box::new(Expression::True),
                Box::new(Expression::False)
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Or,
                Box::new(Expression::False),
                Box::new(NOP_TABLE)
            ))
            .unwrap(),
            NOP_TABLE
        );
    }

    #[test]
    fn binary_equality_consteval() {
        // function/table
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(NOP_TABLE),
                Box::new(NOP_TABLE)
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::NotEqual,
                Box::new(NOP_TABLE),
                Box::new(NOP_FUNCTION)
            ))
            .unwrap(),
            Expression::True
        );

        // identifiers
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(id!("foo")),
                Box::new(id!("foo"))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(id!("foo")),
                Box::new(id!("bar"))
            ))
            .unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(id!("foo")),
                Box::new(id!("bar"))
            )
        );

        // suffixed expressions
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::NamedField("b".to_owned())],
                })),
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::NamedField("b".to_owned())],
                }))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::IndexedField(id!("b"))],
                })),
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::IndexedField(id!("b"))],
                }))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::FunctionCall(vec![
                        Expression::Integer(10),
                        id!("b")
                    ])],
                })),
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::FunctionCall(vec![
                        Expression::Number(10.0),
                        id!("b")
                    ])],
                }))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::MethodCall("foo".to_owned(), vec![])],
                })),
                Box::new(Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("a")),
                    suffixes: vec![Suffix::MethodCall("foo".to_owned(), vec![])],
                }))
            ))
            .unwrap(),
            Expression::True
        );

        // binary expressions
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::Add,
                    Box::new(id!("a")),
                    Box::new(id!("b"))
                )),
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::Add,
                    Box::new(id!("a")),
                    Box::new(id!("b"))
                ))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Nil),
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::And,
                    Box::new(id!("a")),
                    Box::new(id!("b"))
                ))
            ))
            .unwrap(),
            Expression::False
        );

        // unary expressions
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::UnaryOperator(
                    UnaryOperator::Not,
                    Box::new(id!("a"))
                )),
                Box::new(Expression::Nil)
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::UnaryOperator(
                    UnaryOperator::Len,
                    Box::new(id!("a"))
                )),
                Box::new(Expression::String("foo".to_owned()))
            ))
            .unwrap(),
            Expression::False
        );

        // string
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::String("foo".to_owned())),
                Box::new(Expression::String("foo".to_owned()))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::String("foo".to_owned())),
                Box::new(Expression::String("bar".to_owned()))
            ))
            .unwrap(),
            Expression::False
        );

        // Integer/Number
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Integer(101)),
                Box::new(Expression::Integer(101))
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Integer(101)),
                Box::new(Expression::Number(101.1))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Number(1.1)),
                Box::new(Expression::Integer(1))
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Number(1.5)),
                Box::new(Expression::Number(1.5))
            ))
            .unwrap(),
            Expression::True
        );

        // Nil
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::Nil),
                Box::new(Expression::Nil)
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::NotEqual,
                Box::new(Expression::Nil),
                Box::new(Expression::Integer(10))
            ))
            .unwrap(),
            Expression::True
        );

        // True/False
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::False),
                Box::new(Expression::False)
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Equal,
                Box::new(Expression::False),
                Box::new(Expression::True)
            ))
            .unwrap(),
            Expression::False
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::NotEqual,
                Box::new(Expression::False),
                Box::new(Expression::True)
            ))
            .unwrap(),
            Expression::True
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::NotEqual,
                Box::new(Expression::True),
                Box::new(Expression::True)
            ))
            .unwrap(),
            Expression::False
        );
    }

    #[test]
    fn binary_string_concat_consteval() {
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Concat,
                Box::new(Expression::String("foo".to_owned())),
                Box::new(Expression::String("bar".to_owned()))
            ))
            .unwrap(),
            Expression::String("foobar".to_owned())
        );
        assert_eq!(
            consteval_expression(Expression::BinaryOperator(
                BinaryOperator::Concat,
                Box::new(Expression::String("foo".to_owned())),
                Box::new(id!("foo"))
            ))
            .unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::Concat,
                Box::new(Expression::String("foo".to_owned())),
                Box::new(id!("foo"))
            )
        );
    }

    #[test]
    fn illegal_arithmetic() {
        // -nil
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(Expression::Nil)
        ))
        .is_err());

        // -true
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(Expression::True)
        ))
        .is_err());

        // -false
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(Expression::False)
        ))
        .is_err());

        // -"abc"
        // -"123"
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(Expression::String("123".to_owned()))
        ))
        .is_err());

        // - ...
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(Expression::Dots)
        ))
        .is_err());

        // - function() end
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(NOP_FUNCTION)
        ))
        .is_err());

        // -{}
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Minus,
            Box::new(NOP_TABLE)
        ))
        .is_err());
    }

    #[test]
    fn illegal_bitwise_operation() {
        // ~nil
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(Expression::Nil)
        ))
        .is_err());

        // ~true
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(Expression::True)
        ))
        .is_err());

        // ~false
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(Expression::False)
        ))
        .is_err());

        // ~1.5
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(Expression::Number(1.5))
        ))
        .is_err());

        // ~"10"
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(Expression::String("10".to_owned()))
        ))
        .is_err());

        // ~...
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(Expression::Dots)
        ))
        .is_err());

        // ~ function() end
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(NOP_FUNCTION)
        ))
        .is_err());

        // ~ {}
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::BitNot,
            Box::new(NOP_TABLE)
        ))
        .is_err());
    }

    #[test]
    fn illegal_logical_operation() {
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Not,
            Box::new(Expression::Dots)
        ))
        .is_err());
    }

    #[test]
    fn illegal_string_operation() {
        // # nil
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::Nil)
        ))
        .is_err());

        // # true
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::True)
        ))
        .is_err());

        // # false
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::False)
        ))
        .is_err());

        // # 10
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::Integer(10))
        ))
        .is_err());

        // # 0.5
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::Number(0.5))
        ))
        .is_err());

        // # function() end
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(NOP_FUNCTION)
        ))
        .is_err());

        // # {}
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(NOP_TABLE)
        ))
        .is_err());

        // # (unary expression can only produce numeric/boolean value)
        // # (-10)
        // # (not nil)
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::UnaryOperator(
                UnaryOperator::Minus,
                Box::new(Expression::Integer(10))
            ))
        ))
        .is_err());
        assert!(consteval_expression(Expression::UnaryOperator(
            UnaryOperator::Len,
            Box::new(Expression::UnaryOperator(
                UnaryOperator::Not,
                Box::new(Expression::Nil)
            ))
        ))
        .is_err());
    }
}
