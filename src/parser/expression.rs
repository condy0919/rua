use std::io;

use super::{
    get_binary_operator, get_unary_operator, Associativity, BinaryOperator, Block, Parser,
    ParserError, Precedence, UnaryOperator, MIN_OPERATOR_PRECEDENCE,
};
use crate::lexer::Token;

/// An expression in `Lua` can be:
///
/// - `nil`
/// - `true`
/// - `false`
/// - String
/// - `Integer`
/// - `Number`
/// - Table
/// - `...`
/// - Identifier
/// - Expression **BinaryOperator** Expression
/// - **UnaryOperator** Expression
/// - `(` Expression `)`
/// - Function call
///
/// `Integer` and `Number` are explained in **lexer** module.
///
/// `nil`, `true`, `false`, String and Identifier are identical to their
/// **lexer** tokens.
///
/// See [`parse_table_constructor`] for the definition of a Table.
///
/// The precedence of binary operators and unary operators are explained in
/// [`operator`] module.
#[derive(Debug, PartialEq)]
pub enum Expression {
    Nil,
    True,
    False,
    Integer(i64),
    Number(f64),
    Identifier(String),
    String(String),
    Dots,
    Function(FunctionDefinition),
    TableConstructor(TableConstructor),
    Suffixed(SuffixedExpression),
    UnaryOperator(UnaryOperator, Box<Expression>),
    BinaryOperator(BinaryOperator, Box<Expression>, Box<Expression>),
}

/// `SuffixedExpression` is a specical case of `Expression`.
///
/// It can be the following:
///
/// - `a.b` denotes table fields selector. A syntax sugar of `a["b"]`
/// - `a[b]` denotes table indexed selector.
/// - `a.b()` denotes a function call
/// - `a.b:c()` denotes a method call which implies the first parameter is the
///   self
#[derive(Debug, PartialEq)]
pub struct SuffixedExpression {
    pub primary: Box<Expression>,
    pub suffixes: Vec<Suffix>,
}

#[derive(Debug, PartialEq)]
pub enum Suffix {
    NamedField(String),
    IndexedField(Expression),
    FunctionCall(Vec<Expression>),
    MethodCall(String, Vec<Expression>),
}

/// A function definition more likely an anonymous function.
#[derive(Debug, PartialEq)]
pub struct FunctionDefinition {
    pub parameters: Vec<String>,
    pub has_varargs: bool,
    pub body: Block,
}

#[derive(Debug, PartialEq)]
pub struct TableConstructor {
    pub fields: Vec<ConstructorField>,
}

#[derive(Debug, PartialEq)]
pub enum ConstructorField {
    Array(Expression),
    Record(RecordKey, Expression),
}

#[derive(Debug, PartialEq)]
pub enum RecordKey {
    Named(String),
    Indexed(Expression),
}

impl<'a, S: io::Read> Parser<'a, S> {
    /// ```lua
    /// expr ::= subexpr
    /// ```
    pub(crate) fn parse_expression(&mut self) -> Result<Expression, ParserError> {
        self.parse_sub_expression(MIN_OPERATOR_PRECEDENCE)
    }

    /// ```lua
    /// subexpr ::= (simpleexp | unop subexpr) (binop subexpr)*
    /// ```
    ///
    /// where `binop` is any binary operator with a precedence higher than
    /// `min_precedence` or a right-associative operator whose precedence is
    /// equal to `min_precedence`
    ///
    /// Visit https://en.wikipedia.org/wiki/Operator-precedence_parser for more
    /// information.
    fn parse_sub_expression(&mut self, min_precedence: u8) -> Result<Expression, ParserError> {
        let _recursion_guard = self.get_recursion_guard()?;

        let mut lhs = if let Some(unary_op) = self.peek(0)?.and_then(get_unary_operator) {
            self.advance(1);
            Expression::UnaryOperator(
                unary_op,
                Box::new(self.parse_sub_expression(unary_op.precedence().0)?),
            )
        } else {
            self.parse_simple_expression()?
        };

        while let Some(binary_op) = self.peek(0)?.and_then(get_binary_operator) {
            let (precedence, assoc) = binary_op.precedence();
            if precedence < min_precedence
                || precedence == min_precedence && assoc != Associativity::R
            {
                break;
            }

            self.advance(1);
            let rhs = self.parse_sub_expression(precedence)?;
            lhs = Expression::BinaryOperator(binary_op, Box::new(lhs), Box::new(rhs));
        }

        Ok(lhs)
    }

    /// ```lua
    /// simpleexp ::= Number | Integer | String | Nil | True | False | ... |
    /// TableConstructor | FUNCTION body | suffixedexp
    /// ```
    pub(crate) fn parse_simple_expression(&mut self) -> Result<Expression, ParserError> {
        let expr = match self.peek(0)? {
            Some(&Token::Number(n)) => Expression::Number(n),
            Some(&Token::Integer(i)) => Expression::Integer(i),
            Some(&Token::String(ref s)) => Expression::String(s.clone()),
            Some(&Token::Nil) => Expression::Nil,
            Some(&Token::True) => Expression::True,
            Some(&Token::False) => Expression::False,
            Some(&Token::Dots) => Expression::Dots,
            Some(&Token::LeftBrace) => {
                return Ok(Expression::TableConstructor(
                    self.parse_table_constructor()?,
                ));
            }
            Some(&Token::Function) => {
                return Ok(Expression::Function(self.parse_function_definition()?));
            }
            _ => return self.parse_suffixed_expression(),
        };

        self.advance(1);
        Ok(expr)
    }

    /// A suffixed expression can be an `Identifier`, a table field and function calls.
    ///
    /// ```lua
    /// suffixedexp ::= primaryexp ('.' NAME | '[' exp ']' | ':' NAME funcargs | funcargs)*
    /// ```
    ///
    /// # Identifier
    ///
    /// A single name can denote a global variable or a local variable (or a
    /// function's formal parameter, which is a particular kind of local
    /// variable):
    ///
    /// ```lua
    /// var ::= Name
    /// ```
    ///
    /// **Name** denotes identifiers.
    ///
    /// Any variable name is assumed to be global unless explicitly declared as
    /// a local. Local variables are lexically scoped: local variables can be
    /// freely accessed by functions defined inside their scope.
    ///
    /// Before the first assignment to a variable, its value is `nil`.
    ///
    /// # Table field
    ///
    /// Square brackets are used to index a table:
    ///
    /// ```lua
    /// var ::= prefixexp '[' exp ']'
    /// ```
    ///
    /// The meaning of accesses to table fields can be changed via metatables.
    ///
    /// The syntax `var.Name` is just syntactic sugar for `var["Name"]`:
    ///
    /// ```lua
    /// var ::= prefixexp '.' Name
    /// ```
    ///
    /// An access to a global variable `x` is equivalent to `_ENV.x`. Due to the
    /// way that chunks are compiled, `_ENV` is never a global name.
    ///
    /// # Function calls
    ///
    /// A function call in `Lua` has the following syntax:
    ///
    /// ```lua
    /// functioncall ::= prefixexp args
    /// ```
    ///
    /// In a function call, first prefixexp and args are evaluated. If the value
    /// of prefixexp has type function, then this function is called with the
    /// given arguments. Otherwise, the prefixexp "call" metamethod is called,
    /// having as first argument the value of prefixexp, followed by the
    /// original call arguments.
    ///
    /// The form
    ///
    /// ```lua
    /// functioncall ::= prefixexp ':' Name args
    /// ```
    ///
    /// can be used to call "methods". A call `v:name(args)` is syntactic sugar
    /// for `v.name(v,args)`, except that `v` is evaluated only once.
    ///
    /// Arguments have the following syntax:
    ///
    /// ```lua
    /// args ::= '(' (explist)? ')'
    /// args ::= TableConstructor
    /// args ::= LiteralString
    /// ```
    ///
    /// All argument expressions are evaluated before the call. A call of the
    /// form `f{fields}` is syntactic sugar for `f({fields})`; that is, the
    /// argument list is a single new table. A call of the form `f'string'` (or
    /// `f"string"` or `f[[string]]`) is syntactic sugar for `f('string')`; that
    /// is, the argument list is a single literal string.
    pub(crate) fn parse_suffixed_expression(&mut self) -> Result<Expression, ParserError> {
        let primary = self.parse_primary_expression()?;
        let mut suffixes = Vec::new();

        loop {
            match self.peek(0)? {
                Some(&Token::Dot) => {
                    self.expect_next(Token::Dot)?;
                    suffixes.push(Suffix::NamedField(self.expect_identifier()?));
                }
                Some(&Token::LeftBracket) => {
                    self.expect_next(Token::LeftBracket)?;
                    suffixes.push(Suffix::IndexedField(self.parse_expression()?));
                    self.expect_next(Token::RightBracket)?;
                }
                Some(&Token::Colon) => {
                    self.expect_next(Token::Colon)?;
                    let name = self.expect_identifier()?;
                    let args = self.parse_function_args()?;
                    suffixes.push(Suffix::MethodCall(name, args));
                }
                // The prefixes of `funcargs`
                Some(&Token::LeftParen) | Some(&Token::LeftBrace) | Some(&Token::String(_)) => {
                    suffixes.push(Suffix::FunctionCall(self.parse_function_args()?));
                }
                _ => break,
            }
        }

        // Nested structures elimination
        Ok(if suffixes.is_empty() {
            primary
        } else {
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(primary),
                suffixes,
            })
        })
    }

    /// ```lua
    /// primaryexp ::= NAME | '(' expr ')'
    /// ```
    fn parse_primary_expression(&mut self) -> Result<Expression, ParserError> {
        match self.peek(0)? {
            Some(&Token::LeftParen) => {
                self.expect_next(Token::LeftParen)?;
                let expr = self.parse_expression()?;
                self.expect_next(Token::RightParen)?;
                Ok(expr)
            }
            Some(&Token::Identifier(_)) => Ok(Expression::Identifier(self.expect_identifier()?)),
            token => Err(ParserError::Unexpected {
                unexpected: format!("{:?}", token),
                expected: Some("(expr) or Identifier".to_owned()),
            }),
        }
    }

    /// Parses function arguments.
    ///
    /// ```lua
    /// funcargs ::= '(' explist? ')' | TableConstructor | String
    /// ```
    ///
    /// where **explist** is optional.
    pub(crate) fn parse_function_args(&mut self) -> Result<Vec<Expression>, ParserError> {
        Ok(match self.peek(0)? {
            Some(&Token::LeftParen) => match self.peek(1)? {
                Some(&Token::RightParen) => {
                    self.advance(2);
                    vec![]
                }
                _ => {
                    self.expect_next(Token::LeftParen)?;
                    let args = self.parse_expression_list()?;
                    self.expect_next(Token::RightParen)?;
                    args
                }
            },
            Some(&Token::LeftBrace) => vec![Expression::TableConstructor(
                self.parse_table_constructor()?,
            )],
            Some(&Token::String(_)) => vec![Expression::String(self.expect_string()?)],
            token => {
                return Err(ParserError::Unexpected {
                    unexpected: format!("{:?}", token),
                    expected: Some("(explist) | tableconstructor | literalstring".to_owned()),
                })
            }
        })
    }

    /// Table constructors are expressions that create tables. Every time a
    /// constructor is evaluated, a new table is created. A constructor can be
    /// used to create an empty table or to create a table and initialize some
    /// of its fields. The general syntax for constructors is
    ///
    /// ```lua
    /// tableconstructor ::= '{' [fieldlist] '}'
    /// fieldlist ::= field {fieldsep field} [fieldsep]
    /// field ::= '[' exp ']' '=' exp | Name '=' exp | exp
    /// fieldsep ::= ',' | ';'
    /// ```
    ///
    /// Each field of the form [exp1] = exp2 adds to the new table an entry with
    /// key exp1 and value exp2. A field of the form name = exp is equivalent to
    /// ["name"] = exp. Finally, fields of the form exp are equivalent to [i] =
    /// exp, where i are consecutive integers starting with 1. Fields in the
    /// other formats do not affect this counting. For example,
    ///
    /// ```lua
    /// a = { [f(1)] = g; "x", "y"; x = 1, f(x), [30] = 23; 45 }
    /// ```
    ///
    /// is equivalent to
    ///
    /// ```lua
    /// do
    ///    local t = {}
    ///    t[f(1)] = g
    ///    t[1] = "x"         -- 1st exp
    ///    t[2] = "y"         -- 2nd exp
    ///    t.x = 1            -- t["x"] = 1
    ///    t[3] = f(x)        -- 3rd exp
    ///    t[30] = 23
    ///    t[4] = 45          -- 4th exp
    ///    a = t
    /// end
    /// ```
    ///
    /// The order of the assignments in a constructor is undefined. (This order
    /// would be relevant only when there are repeated keys.)
    ///
    /// If the last field in the list has the form exp and the expression is a
    /// function call or a vararg expression, then all values returned by this
    /// expression enter the list consecutively.
    ///
    /// The field list can have an optional trailing separator, as a convenience
    /// for machine-generated code.
    pub(crate) fn parse_table_constructor(&mut self) -> Result<TableConstructor, ParserError> {
        self.expect_next(Token::LeftBrace)?;
        let mut fields = Vec::new();
        while self.peek(0)? != Some(&Token::RightBrace) {
            match self.peek(0)? {
                Some(&Token::Comma) | Some(&Token::SemiColon) => {
                    if fields.is_empty() {
                        return Err(ParserError::Unexpected {
                            unexpected: format!("comma or semicolon after {{"),
                            expected: None,
                        });
                    }

                    self.advance(1);
                }
                Some(&Token::LeftBracket) => {
                    self.expect_next(Token::LeftBracket)?;
                    let key = self.parse_expression()?;
                    self.expect_next(Token::RightBracket)?;
                    self.expect_next(Token::Assign)?;
                    let value = self.parse_expression()?;
                    fields.push(ConstructorField::Record(RecordKey::Indexed(key), value));
                }
                Some(&Token::Identifier(_)) => match self.peek(1)? {
                    Some(&Token::Assign) => {
                        let name = self.expect_identifier()?;
                        self.expect_next(Token::Assign)?;
                        let value = self.parse_expression()?;
                        fields.push(ConstructorField::Record(RecordKey::Named(name), value));
                    }
                    _ => {
                        fields.push(ConstructorField::Array(self.parse_expression()?));
                    }
                },
                _ => {
                    fields.push(ConstructorField::Array(self.parse_expression()?));
                }
            }
        }

        self.expect_next(Token::RightBrace)?;
        Ok(TableConstructor { fields })
    }

    /// Parse an expression list.
    ///
    /// An expression list consists of expressions. `,` (Comma) is used as the
    /// expression separator.
    ///
    /// It can be described in **EBNF** notation:
    ///
    /// ```lua
    /// explist ::= exp (',' exp)*
    /// ```
    pub(crate) fn parse_expression_list(&mut self) -> Result<Vec<Expression>, ParserError> {
        let mut exprs = Vec::new();
        exprs.push(self.parse_expression()?);
        while self.peek(0)? == Some(&Token::Comma) {
            self.advance(1);
            exprs.push(self.parse_expression()?);
        }

        Ok(exprs)
    }

    /// Parses a function body.
    ///
    /// See `parse_function_definition` for more information.
    pub(crate) fn parse_function_body(&mut self) -> Result<FunctionDefinition, ParserError> {
        self.expect_next(Token::LeftParen)?;

        let mut parameters = Vec::new();
        let mut has_varargs = false;
        while self.peek(0)? != Some(&Token::RightParen) {
            match self.peek(0)? {
                Some(&Token::Dots) => {
                    has_varargs = true;
                    self.advance(1);
                }
                Some(&Token::Identifier(ref s)) => {
                    parameters.push(s.clone());
                    self.advance(1);
                }
                Some(&Token::Comma) => {
                    self.advance(1);
                }
                other => {
                    return Err(ParserError::Unexpected {
                        unexpected: format!("{:?}", other),
                        expected: Some("parameters, '...' or ','".to_owned()),
                    });
                }
            }
        }

        self.expect_next(Token::RightParen)?;

        let body = self.parse_block()?;
        self.expect_next(Token::End)?;

        Ok(FunctionDefinition {
            parameters,
            has_varargs,
            body,
        })
    }

    /// The syntax for function definition is
    ///
    /// ```lua
    /// FunctionDefinition ::= function funcbody
    /// funcbody ::= '(' parlist? ‘)’ block end
    /// ```
    ///
    /// # Note
    ///
    /// A function definition is an executable expression, whose value has type
    /// function. When Lua precompiles a chunk, all its function bodies are
    /// precompiled too. Then, whenever Lua executes the function definition,
    /// the function is instantiated (or closed). This function instance (or
    /// closure) is the final value of the expression.
    ///
    /// Parameters act as local variables that are initialized with the argument
    /// values:
    ///
    /// ```lua
    /// parlist ::= namelist (',' '...')? | '...'
    /// ```
    ///
    /// # Function calls
    ///
    /// When a function is called, the list of arguments is adjusted to the
    /// length of the list of parameters, unless the function is a vararg
    /// function, which is indicated by three dots ('...') at the end of its
    /// parameter list. A vararg function does not adjust its argument list;
    /// instead, it collects all extra arguments and supplies them to the
    /// function through a vararg expression, which is also written as three
    /// dots. The value of this expression is a list of all actual extra
    /// arguments, similar to a function with multiple results. If a vararg
    /// expression is used inside another expression or in the middle of a list
    /// of expressions, then its return list is adjusted to one element. If the
    /// expression is used as the last element of a list of expressions, then no
    /// adjustment is made (unless that last expression is enclosed in
    /// parentheses).
    pub(crate) fn parse_function_definition(&mut self) -> Result<FunctionDefinition, ParserError> {
        self.expect_next(Token::Function)?;
        self.parse_function_body()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! id {
        ($name:expr) => {
            Expression::Identifier($name.to_owned())
        };
    }

    const EPS: f64 = 1e-5;
    fn float_equal(exp: Expression, f: f64) -> bool {
        match exp {
            Expression::Number(n) => (n - f).abs() < EPS,
            _ => false,
        }
    }

    #[test]
    fn primitive_values() {
        let mut s: &[u8] = br"42 0xf10 1.5 'a string' nil true false ... anonymous";
        let mut parser = Parser::new(&mut s);
        assert_eq!(parser.parse_expression().unwrap(), Expression::Integer(42));
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::Integer(0xf10)
        );
        assert!(float_equal(parser.parse_expression().unwrap(), 1.5));
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::String("a string".to_owned())
        );
        assert_eq!(parser.parse_expression().unwrap(), Expression::Nil);
        assert_eq!(parser.parse_expression().unwrap(), Expression::True);
        assert_eq!(parser.parse_expression().unwrap(), Expression::False);
        assert_eq!(parser.parse_expression().unwrap(), Expression::Dots);
        assert_eq!(parser.parse_expression().unwrap(), id!("anonymous"));
    }

    #[test]
    fn simple_tableconstructor() {
        let mut s: &[u8] = br#"{[1]=2,"x","y";x=1,y=1;45}"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_table_constructor().unwrap(),
            TableConstructor {
                fields: vec![
                    ConstructorField::Record(
                        RecordKey::Indexed(Expression::Integer(1)),
                        Expression::Integer(2)
                    ),
                    ConstructorField::Array(Expression::String("x".to_owned())),
                    ConstructorField::Array(Expression::String("y".to_owned())),
                    ConstructorField::Record(
                        RecordKey::Named("x".to_owned()),
                        Expression::Integer(1)
                    ),
                    ConstructorField::Record(
                        RecordKey::Named("y".to_owned()),
                        Expression::Integer(1)
                    ),
                    ConstructorField::Array(Expression::Integer(45)),
                ],
            }
        );

        let mut s: &[u8] = b"{; 2; 3; }";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_table_constructor().unwrap_err(),
            ParserError::Unexpected {
                unexpected: format!("comma or semicolon after {{"),
                expected: None
            }
        );
    }

    #[test]
    fn function_definition() {
        let mut s: &[u8] = br#"function() end"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_function_definition().unwrap(),
            FunctionDefinition {
                parameters: vec![],
                has_varargs: false,
                body: Block {
                    stmts: vec![],
                    retstmt: None,
                },
            }
        );

        let mut s: &[u8] = br#"function(a) end"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_function_definition().unwrap(),
            FunctionDefinition {
                parameters: vec!["a".to_owned()],
                has_varargs: false,
                body: Block {
                    stmts: vec![],
                    retstmt: None
                }
            }
        );

        let mut s: &[u8] = br#"function(a,b,c,...) end"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_function_definition().unwrap(),
            FunctionDefinition {
                parameters: vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
                has_varargs: true,
                body: Block {
                    stmts: vec![],
                    retstmt: None
                }
            }
        );

        let mut s: &[u8] = br#"function(...) end"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_function_definition().unwrap(),
            FunctionDefinition {
                parameters: vec![],
                has_varargs: true,
                body: Block {
                    stmts: vec![],
                    retstmt: None
                }
            }
        );
    }

    #[test]
    fn suffixed_expression() {
        let mut s: &[u8] = br#"a.b.c.d a[b].c[d]"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("a")),
                suffixes: vec![
                    Suffix::NamedField("b".to_owned()),
                    Suffix::NamedField("c".to_owned()),
                    Suffix::NamedField("d".to_owned()),
                ],
            })
        );

        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("a")),
                suffixes: vec![
                    Suffix::IndexedField(id!("b")),
                    Suffix::NamedField("c".to_owned()),
                    Suffix::IndexedField(id!("d"))
                ]
            })
        );

        // syntax sugar
        let mut s: &[u8] = br#"f1() f2'string' f3"string" f4[[string]] f5{1,2}"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("f1")),
                suffixes: vec![Suffix::FunctionCall(vec![]),]
            })
        );
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("f2")),
                suffixes: vec![Suffix::FunctionCall(vec![Expression::String(
                    "string".to_owned()
                )])]
            })
        );
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("f3")),
                suffixes: vec![Suffix::FunctionCall(vec![Expression::String(
                    "string".to_owned()
                )])]
            })
        );
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("f4")),
                suffixes: vec![Suffix::FunctionCall(vec![Expression::String(
                    "string".to_owned()
                )])]
            })
        );
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("f5")),
                suffixes: vec![Suffix::FunctionCall(vec![Expression::TableConstructor(
                    TableConstructor {
                        fields: vec![
                            ConstructorField::Array(Expression::Integer(1)),
                            ConstructorField::Array(Expression::Integer(2)),
                        ]
                    }
                )])]
            })
        );

        // method calls
        let mut s: &[u8] = br#"obj:method1(a)"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("obj")),
                suffixes: vec![Suffix::MethodCall("method1".to_owned(), vec![id!("a")])],
            })
        );

        // function call chains
        let mut s: &[u8] = br#"f(a)(b)(c)"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_suffixed_expression().unwrap(),
            Expression::Suffixed(SuffixedExpression {
                primary: Box::new(id!("f")),
                suffixes: vec![
                    Suffix::FunctionCall(vec![id!("a")]),
                    Suffix::FunctionCall(vec![id!("b")]),
                    Suffix::FunctionCall(vec![id!("c")])
                ],
            })
        );
    }

    #[test]
    fn unary_operator() {
        let mut s: &[u8] = b"-1";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::UnaryOperator(UnaryOperator::Minus, Box::new(Expression::Integer(1)))
        );

        let mut s: &[u8] = b"not false";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::UnaryOperator(UnaryOperator::Not, Box::new(Expression::False))
        );

        let mut s: &[u8] = b"~0";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::UnaryOperator(UnaryOperator::BitNot, Box::new(Expression::Integer(0)))
        );

        let mut s: &[u8] = b"#'empty'";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::UnaryOperator(
                UnaryOperator::Len,
                Box::new(Expression::String("empty".to_owned()))
            )
        );
    }

    #[test]
    fn binary_operator() {
        let mut s: &[u8] = b"a+b";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperator(BinaryOperator::Add, Box::new(id!("a")), Box::new(id!("b")))
        );

        let mut s: &[u8] = b"(a + b) * c - d";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::Sub,
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::Mul,
                    Box::new(Expression::BinaryOperator(
                        BinaryOperator::Add,
                        Box::new(id!("a")),
                        Box::new(id!("b"))
                    )),
                    Box::new(id!("c"))
                )),
                Box::new(id!("d"))
            )
        );

        let mut s: &[u8] = b"a + b * c - d";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::Sub,
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::Add,
                    Box::new(id!("a")),
                    Box::new(Expression::BinaryOperator(
                        BinaryOperator::Mul,
                        Box::new(id!("b")),
                        Box::new(id!("c"))
                    )),
                )),
                Box::new(id!("d"))
            )
        );

        let mut s: &[u8] = b"a * -b ^ c - d";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::Sub,
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::Mul,
                    Box::new(id!("a")),
                    Box::new(Expression::UnaryOperator(
                        UnaryOperator::Minus,
                        Box::new(Expression::BinaryOperator(
                            BinaryOperator::Power,
                            Box::new(id!("b")),
                            Box::new(id!("c"))
                        ))
                    ))
                )),
                Box::new(id!("d"))
            )
        );

        let mut s: &[u8] = b"(1 < 2 and 2 > 1) ~= true";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::NotEqual,
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::And,
                    Box::new(Expression::BinaryOperator(
                        BinaryOperator::LessThan,
                        Box::new(Expression::Integer(1)),
                        Box::new(Expression::Integer(2))
                    )),
                    Box::new(Expression::BinaryOperator(
                        BinaryOperator::GreaterThan,
                        Box::new(Expression::Integer(2)),
                        Box::new(Expression::Integer(1))
                    ))
                )),
                Box::new(Expression::True)
            )
        );

        // illegal actually
        let mut s: &[u8] = br#"("abc" .. "def") + -(1 // 0)^4>>2 ~ 1 "#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperator(
                BinaryOperator::BitXor,
                Box::new(Expression::BinaryOperator(
                    BinaryOperator::ShiftRight,
                    Box::new(Expression::BinaryOperator(
                        BinaryOperator::Add,
                        Box::new(Expression::BinaryOperator(
                            BinaryOperator::Concat,
                            Box::new(Expression::String("abc".to_owned())),
                            Box::new(Expression::String("def".to_owned()))
                        )),
                        Box::new(Expression::UnaryOperator(
                            UnaryOperator::Minus,
                            Box::new(Expression::BinaryOperator(
                                BinaryOperator::Power,
                                Box::new(Expression::BinaryOperator(
                                    BinaryOperator::IDiv,
                                    Box::new(Expression::Integer(1)),
                                    Box::new(Expression::Integer(0))
                                )),
                                Box::new(Expression::Integer(4))
                            ))
                        ))
                    )),
                    Box::new(Expression::Integer(2))
                )),
                Box::new(Expression::Integer(1))
            )
        );
    }
}
