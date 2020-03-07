use super::{BinaryOperator, Expression, ParserError, UnaryOperator};

///
pub fn consteval_expression(expr: Expression) -> Result<Expression, ParserError> {
    match &expr {
        Expression::UnaryOperator(_, _) => consteval_unary_expression(expr),
        Expression::BinaryOperator(_, _, _) => consteval_binary_expression(expr),
        _ => unreachable!(),
    }
}

// Evaluate unary arithmetic/logical/string operations in compile time.
fn consteval_unary_expression(expr: Expression) -> Result<Expression, ParserError> {
    match &expr {
        Expression::UnaryOperator(UnaryOperator::Minus, subexpr) => match subexpr.as_ref() {
            // Perform unary arithmetic minus operation on an invalid argument
            Expression::Nil => Err(ParserError::Unexpected {
                unexpected: format!("nil value"),
                expected: None,
            }),
            Expression::True | Expression::False => Err(ParserError::Unexpected {
                unexpected: format!("boolean value"),
                expected: None,
            }),
            // Convertion from **String** to **Numeric** is insane.
            //
            // NOTE Incompatible with Lua 5.3
            Expression::String(_) => Err(ParserError::Unexpected {
                unexpected: format!("string value"),
                expected: None,
            }),
            Expression::Dots => Err(ParserError::Unexpected {
                unexpected: format!("'...'"),
                expected: None,
            }),
            Expression::Function(_) => Err(ParserError::Unexpected {
                unexpected: format!("function value"),
                expected: None,
            }),
            Expression::TableConstructor(_) => Err(ParserError::Unexpected {
                unexpected: format!("table value"),
                expected: None,
            }),

            // minus minus optimization
            Expression::UnaryOperator(UnaryOperator::Minus, _) => {
                if let Expression::UnaryOperator(_, sub) = expr {
                    if let Expression::UnaryOperator(_, v) = *sub {
                        return Ok(*v);
                    }
                }
                unreachable!()
            }

            &Expression::Integer(i) => Ok(Expression::Integer(-i)),
            &Expression::Number(n) => Ok(Expression::Number(-n)),

            // Identifier, FunctionCall, TableFieldAccess or other unary/binary
            // expressions
            _ => Ok(expr),
        },
        Expression::UnaryOperator(UnaryOperator::BitNot, subexpr) => match subexpr.as_ref() {
            // Perform unary bitwise not operation on an invalid argument
            Expression::Nil => Err(ParserError::Unexpected {
                unexpected: format!("nil value"),
                expected: None,
            }),
            Expression::True | Expression::False => Err(ParserError::Unexpected {
                unexpected: format!("boolean value"),
                expected: None,
            }),
            Expression::Number(_) => Err(ParserError::Unexpected {
                unexpected: format!("float value"),
                expected: None,
            }),
            Expression::String(_) => Err(ParserError::Unexpected {
                unexpected: format!("string value"),
                expected: None,
            }),
            Expression::Dots => Err(ParserError::Unexpected {
                unexpected: format!("'...'"),
                expected: None,
            }),
            Expression::Function(_) => Err(ParserError::Unexpected {
                unexpected: format!("function value"),
                expected: None,
            }),
            Expression::TableConstructor(_) => Err(ParserError::Unexpected {
                unexpected: format!("table value"),
                expected: None,
            }),

            // bitnot bitnor optimization
            Expression::UnaryOperator(UnaryOperator::BitNot, _) => {
                if let Expression::UnaryOperator(_, sub) = expr {
                    if let Expression::UnaryOperator(_, v) = *sub {
                        return Ok(*v);
                    }
                }
                unreachable!()
            }

            &Expression::Integer(i) => Ok(Expression::Integer(!i)),

            _ => Ok(expr),
        },
        Expression::UnaryOperator(UnaryOperator::Not, subexpr) => match subexpr.as_ref() {
            // Perform unary logical not operation on an invalid argument
            Expression::Dots => Err(ParserError::Unexpected {
                unexpected: format!("'...'"),
                expected: None,
            }),

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
            Expression::UnaryOperator(UnaryOperator::Not, _) => {
                if let Expression::UnaryOperator(_, sub) = expr {
                    if let Expression::UnaryOperator(_, v) = *sub {
                        return Ok(*v);
                    }
                }
                unreachable!()
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
        },
        Expression::UnaryOperator(UnaryOperator::Len, subexpr) => match subexpr.as_ref() {
            // Perform unary string length operation on an invalid argument
            Expression::Nil => Err(ParserError::Unexpected {
                unexpected: format!("nil value"),
                expected: None,
            }),
            Expression::True | Expression::False => Err(ParserError::Unexpected {
                unexpected: format!("boolean value"),
                expected: None,
            }),
            Expression::Integer(_) | Expression::Number(_) => Err(ParserError::Unexpected {
                unexpected: format!("number value"),
                expected: None,
            }),
            Expression::Dots => Err(ParserError::Unexpected {
                unexpected: format!("'...'"),
                expected: None,
            }),
            Expression::Function(_) => Err(ParserError::Unexpected {
                unexpected: format!("function value"),
                expected: None,
            }),
            Expression::TableConstructor(_) => Err(ParserError::Unexpected {
                unexpected: format!("table value"),
                expected: None,
            }),
            Expression::UnaryOperator(_, _) => Err(ParserError::Unexpected {
                unexpected: format!("prefixed with an unary operator expression"),
                expected: None,
            }),

            Expression::String(s) => Ok(Expression::Integer(s.len() as i64)),

            _ => Ok(expr),
        },
        _ => unreachable!(),
    }
}

// Eval binary arithmetic/logical/string operations in compile time.
fn consteval_binary_expression(expr: Expression) -> Result<Expression, ParserError> {
    todo!()
}
