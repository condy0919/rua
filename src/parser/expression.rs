use std::io;

use super::{Block, Parser, ParserError};
use crate::lexer::Token;

/// TODO document me
#[derive(Debug, PartialEq)]
pub enum Expression {
    Nil,
    True,
    False,
    Integer(i64),
    Number(f64),
    String(String),
    Dots,
    //     | functiondef
    //     | prefixexp
    //     | tableconstructor
    //     | <assoc=right> exp operatorPower exp
    //     | operatorUnary exp
    //     | exp operatorMulDivMod exp
    //     | exp operatorAddSub exp
    //     | <assoc=right> exp operatorStrcat exp
    //     | exp operatorComparison exp
    //     | exp operatorAnd exp
    //     | exp operatorOr exp
    //     | exp operatorBitwise exp
    //     ;
}

#[derive(Debug, PartialEq)]
pub struct FunctionDefinition {
    pub parameters: Vec<String>,
    pub has_varargs: bool,
    pub body: Block,
}

impl<'a, S: io::Read> Parser<'a, S> {
    /// TODO document me
    pub(crate) fn parse_expression(&mut self) -> Result<Expression, ParserError> {
        todo!()
    }

    /// Parse an expression list.
    ///
    /// An expression list consists of expressions. `,` (Comma) is used as the
    /// expression separator.
    ///
    /// It can be described in **EBNF** notation:
    ///
    /// explist := exp (',' exp)*
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
                Some(Token::Identifier(s)) => {
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
    /// FunctionDefinition := **function** funcbody
    /// funcbody := '(' parlist? ‘)’ block **end**
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
    /// parlist := namelist (',' '...')? | '...'
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
