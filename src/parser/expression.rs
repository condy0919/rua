use std::io;

use super::{
    get_binary_operator, get_unary_operator, BinaryOperator, Block, Parser, ParserError,
    Precedence, UnaryOperator, MIN_OPERATOR_PRECEDENCE,
};
use crate::lexer::Token;

/// TODO document me
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
    FunctionCall(Box<FunctionCall>),
    MethodCall(Box<MethodCall>),
    TableConstructor(TableConstructor),
    UnaryOperator(UnaryOperator, Box<Expression>),
    BinaryOperator(BinaryOperator, Box<Expression>, Box<Expression>),
}

#[derive(Debug, PartialEq)]
pub struct FunctionDefinition {
    pub parameters: Vec<String>,
    pub has_varargs: bool,
    pub body: Block,
}

#[derive(Debug, PartialEq)]
pub struct FunctionCall {
    pub func: Expression,
    pub args: Vec<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct MethodCall {
    pub obj: Expression,
    pub method: String,
    pub args: Vec<Expression>,
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
    /// TODO document me
    /// expr -> subexpr
    pub(crate) fn parse_expression(&mut self) -> Result<Expression, ParserError> {
        self.parse_sub_expression(MIN_OPERATOR_PRECEDENCE)
    }

    /// subexpr -> (simpleexp | unop subexpr) { binop subexpr }
    ///
    /// where 'binop' is any binary operator with a priority higher than
    /// 'min_precedence'
    fn parse_sub_expression(&mut self, min_precedence: u8) -> Result<Expression, ParserError> {
        let _recursion_guard = self.get_recursion_guard()?;

        let _expr = if let Some(unary_op) = self.peek(0)?.and_then(get_unary_operator) {
            self.advance(1);
            Expression::UnaryOperator(
                unary_op,
                Box::new(self.parse_sub_expression(unary_op.precedence().0)?),
            )
        } else {
            self.parse_simple_expression()?
        };

        //
        // static BinOpr subexpr (LexState *ls, expdesc *v, int limit) {
        //   BinOpr op;
        //   UnOpr uop;
        //   enterlevel(ls);
        //   uop = getunopr(ls->t.token);
        //   if (uop != OPR_NOUNOPR) {
        //     int line = ls->linenumber;
        //     luaX_next(ls);
        //     subexpr(ls, v, UNARY_PRIORITY);
        //     luaK_prefix(ls->fs, uop, v, line);
        //   }
        //   else simpleexp(ls, v);
        //   /* expand while operators have priorities higher than 'limit' */
        //   op = getbinopr(ls->t.token);
        //   while (op != OPR_NOBINOPR && priority[op].left > limit) {
        //     expdesc v2;
        //     BinOpr nextop;
        //     int line = ls->linenumber;
        //     luaX_next(ls);
        //     luaK_infix(ls->fs, op, v);
        //     /* read sub-expression with higher priority */
        //     nextop = subexpr(ls, &v2, priority[op].right);
        //     luaK_posfix(ls->fs, op, v, &v2, line);
        //     op = nextop;
        //   }
        //   leavelevel(ls);
        //   return op;  /* return first untreated operator */
        // }
        todo!()
    }

    /// simpleexp -> FLT | INT | STRING | NIL | TRUE | FALSE | ... |
    /// tableconstructor | FUNCTION body | suffixedexp
    fn parse_simple_expression(&mut self) -> Result<Expression, ParserError> {
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

    /// suffixedexp -> primaryexp { '.' NAME | '[' exp ']' | ':' NAME funcargs | funcargs }
    fn parse_suffixed_expression(&mut self) -> Result<Expression, ParserError> {
        let exp = self.parse_primary_expression()?;

        match self.peek(0)? {
            Some(&Token::Dot) => {}
            Some(&Token::LeftBracket) => {}
            Some(&Token::Colon) => {} // TODO funcargs
            _ => {}
        };
        todo!()
    }

    /// primaryexp -> NAME | '(' expr ')'
    fn parse_primary_expression(&mut self) -> Result<Expression, ParserError> {
        match self.peek(0)? {
            Some(&Token::LeftBrace) => {
                self.expect_next(Token::LeftBrace)?;
                let expr = self.parse_expression()?;
                self.expect_next(Token::RightBrace)?;
                Ok(expr)
            }
            Some(&Token::Identifier(_)) => Ok(Expression::Identifier(self.expect_identifier()?)),
            token => Err(ParserError::Unexpected {
                unexpected: format!("{:?}", token),
                expected: Some("'(' or Identifier".to_owned()),
            }),
        }
    }

    ///
    /// funcargs -> '(' explist? ')' | tableconstructor | literalstring
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
