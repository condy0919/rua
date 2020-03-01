use std::io;

use super::{Block, Expression, FunctionDefinition, Parser, ParserError};
use crate::lexer::Token;

///
#[derive(Debug, PartialEq)]
pub enum Statement {
    // : ';'
    //     | varlist '=' explist
    //     | functioncall
    Label(String),
    Break,
    Goto(String),
    Do(Block),
    While(WhileStatement),
    Repeat(RepeatStatement),
    If(IfStatement),
    For(ForStatement),
    Function(FunctionStatement),
    LocalFunction(LocalFunctionStatement),
    LocalDeclaration(LocalDeclarationStatement),
}

#[derive(Debug, PartialEq)]
pub struct ReturnStatement {
    pub returns: Vec<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct WhileStatement {
    pub condition: Expression,
    pub block: Block,
}

#[derive(Debug, PartialEq)]
pub struct RepeatStatement {
    pub block: Block,
    pub until: Expression,
}

#[derive(Debug, PartialEq)]
pub struct IfStatement {
    pub if_then: (Expression, Block),
    pub some_elseif_then: Vec<(Expression, Block)>,
    pub else_: Option<Block>,
}

#[derive(Debug, PartialEq)]
pub enum ForStatement {
    Numeric {
        name: String,
        initial: Expression,
        limit: Expression,
        step: Option<Expression>,
        block: Block,
    },
    Generic {
        names: Vec<String>,
        values: Vec<Expression>,
        block: Block,
    },
}

#[derive(Debug, PartialEq)]
pub struct FunctionStatement {
    pub name: String,
    pub fields: Vec<String>,
    pub method: Option<String>,
    pub definition: FunctionDefinition,
}

#[derive(Debug, PartialEq)]
pub struct LocalFunctionStatement {
    pub name: String,
    pub definition: FunctionDefinition,
}

#[derive(Debug, PartialEq)]
pub struct LocalDeclarationStatement {
    pub names: Vec<String>,
    pub values: Vec<Expression>,
}

impl<'a, S: io::Read> Parser<'a, S> {
    /// TODO document me
    pub(crate) fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        let _recursion_guard = self.get_recursion_guard();

        Ok(match self.peek(0)? {
            Some(&Token::DoubleColon) => {
                self.expect_next(Token::DoubleColon)?;
                let name = self.expect_identifier()?;
                self.expect_next(Token::DoubleColon)?;
                Statement::Label(name)
            }
            Some(&Token::Break) => {
                self.expect_next(Token::Break)?;
                Statement::Break
            }
            Some(&Token::Goto) => {
                self.expect_next(Token::Goto)?;
                Statement::Goto(self.expect_identifier()?)
            }
            Some(&Token::Do) => {
                self.expect_next(Token::Do)?;
                let block = self.parse_block()?;
                self.expect_next(Token::End)?;
                Statement::Do(block)
            }
            Some(&Token::While) => Statement::While(self.parse_while_statement()?),
            Some(&Token::Repeat) => Statement::Repeat(self.parse_repeat_statement()?),
            Some(&Token::If) => Statement::If(self.parse_if_statement()?),
            Some(&Token::For) => Statement::For(self.parse_for_statement()?),
            Some(&Token::Function) => Statement::Function(self.parse_function_statement()?),
            Some(&Token::Local) => match self.peek(1)? {
                Some(&Token::Function) => {
                    Statement::LocalFunction(self.parse_local_function_statement()?)
                }
                _ => Statement::LocalDeclaration(self.parse_local_declaration_statement()?),
            },
            // functioncall | assignment
            _ => self.parse_expression_statement()?,
        })
    }

    /// TODO
    pub(crate) fn parse_expression_statement(&mut self) -> Result<Statement, ParserError> {
        todo!()
    }

    /// Parses an return statement.
    ///
    /// As return statement is the last lex of a block, and block can be in the
    /// following structures:
    ///
    /// 1. **while** expression **do** block **end**
    /// 2. **repeat** block **until** expression
    /// 3. **if** expression **then** block **else** block **end**
    /// 4. **if** expression **then** block **elseif** expression **then** block **end**
    /// 5. **do** block **end** in **for**loop or standalone
    /// 6. and function body
    ///
    /// The table is taken from `parse_block`.
    pub(crate) fn parse_return_statement(&mut self) -> Result<ReturnStatement, ParserError> {
        self.expect_next(Token::Return)?;
        let returns = match self.peek(0)? {
            Some(&Token::End)
            | Some(&Token::Until)
            | Some(&Token::Else)
            | Some(&Token::ElseIf)
            | Some(&Token::SemiColon)
            | None => Vec::new(),
            _ => self.parse_expression_list()?,
        };

        if self.peek(0)? == Some(&Token::SemiColon) {
            self.advance(1);
        }

        Ok(ReturnStatement { returns })
    }

    /// The control structure **while** has the usual meaning.
    ///
    /// ```lua
    /// while expression do block end
    /// ```
    /// # Cautious
    ///
    /// The condition expression of a control structure can return any value.
    /// Both **false** and **nil** are considered _false_. All values different
    /// from **nil** and **false** are considered _true_ (in particular, the
    /// number 0 and the empty string are also true).
    pub(crate) fn parse_while_statement(&mut self) -> Result<WhileStatement, ParserError> {
        self.expect_next(Token::While)?;
        let condition = self.parse_expression()?;
        self.expect_next(Token::Do)?;
        let block = self.parse_block()?;
        self.expect_next(Token::End)?;

        Ok(WhileStatement { condition, block })
    }

    /// The control structure **repeat** has the usual meaning.
    ///
    /// ```lua
    /// repeat block until expression
    /// ```
    ///
    /// In the repeat–until loop, the inner block does not end at the **until**
    /// keyword, but only after the condition. So, the condition can refer to
    /// local variables declared inside the loop block.
    ///
    /// # Cautious
    ///
    /// The condition expression of a control structure can return any value.
    /// Both **false** and **nil** are considered _false_. All values different
    /// from **nil** and **false** are considered _true_ (in particular, the
    /// number 0 and the empty string are also true).
    pub(crate) fn parse_repeat_statement(&mut self) -> Result<RepeatStatement, ParserError> {
        self.expect_next(Token::Repeat)?;
        let block = self.parse_block()?;
        self.expect_next(Token::Until)?;
        let until = self.parse_expression()?;

        Ok(RepeatStatement { block, until })
    }

    /// The control structure **if** has the usual meaning.
    ///
    /// ```lua
    /// if expression then block (elseif expression then block)* (else block)? end
    /// ```
    ///
    /// # Cautious
    ///
    /// The condition expression of a control structure can return any value.
    /// Both **false** and **nil** are considered _false_. All values different
    /// from **nil** and **false** are considered _true_ (in particular, the
    /// number 0 and the empty string are also true).
    pub(crate) fn parse_if_statement(&mut self) -> Result<IfStatement, ParserError> {
        self.expect_next(Token::If)?;
        let if_then_cond = self.parse_expression()?;
        self.expect_next(Token::Then)?;
        let if_then_block = self.parse_block()?;
        let if_then = (if_then_cond, if_then_block);

        let mut some_elseif_then = Vec::new();
        while self.peek(0)? == Some(&Token::ElseIf) {
            self.expect_next(Token::ElseIf)?;
            let expr = self.parse_expression()?;
            self.expect_next(Token::Then)?;
            let block = self.parse_block()?;
            some_elseif_then.push((expr, block));
        }

        let else_ = if self.peek(0)? == Some(&Token::Else) {
            self.expect_next(Token::Else)?;
            Some(self.parse_block()?)
        } else {
            None
        };

        self.expect_next(Token::End)?;

        Ok(IfStatement {
            if_then,
            some_elseif_then,
            else_,
        })
    }

    /// The for statement has two forms
    ///
    /// # Numeric form
    ///
    /// The numerical for loop repeats a block of code while a control variable
    /// runs through an arithmetic progression. It has the following syntax:
    ///
    /// ```lua
    /// for Name '=' expression ',' expression (',' expression)? do block end
    /// ```
    ///
    /// The _block_ is repeated for name starting at the value of the first
    /// expression, until it passes the second expression by steps of the third
    /// expression.
    ///
    /// ## Note
    ///
    /// - All three control expressions are evaluated only once, before the loop
    /// starts. They must all result in numbers.
    /// - _initial_, _limit_, and _step_ are invisible variables. The names
    /// shown here are for explanatory purposes only.
    /// - If the third expression (the _step_) is absent, then a step of **1**
    /// is used.
    /// - You can use **break** and **goto** to exit a for loop. The loop
    /// variable _v_ is local to the loop body. If you need its value after the
    /// loop, assign it to another variable before exiting the loop.
    ///
    /// # Generic form
    ///
    /// The generic for statement works over functions, called iterators. On
    /// each iteration, the iterator function is called to produce a new value,
    /// stopping when this new value is **nil**.
    ///
    /// ```lua
    /// for namelist in explist do block end
    /// ```
    ///
    /// ## Note
    ///
    /// - explist is evaluated only once. Its results are an iterator function, a
    /// state, and an initial value for the first iterator variable.
    /// - You can use **break** to exit a for loop.
    /// - The loop variables var_i are local to the loop; you cannot use their
    /// values after the for ends. If you need these values, then assign them to
    /// other variables before breaking or exiting the loop.
    pub(crate) fn parse_for_statement(&mut self) -> Result<ForStatement, ParserError> {
        self.expect_next(Token::For)?;
        let name = self.expect_identifier()?;

        match self.peek(0)? {
            Some(&Token::Assign) => {
                self.expect_next(Token::Assign)?;
                let initial = self.parse_expression()?;
                self.expect_next(Token::Comma)?;
                let limit = self.parse_expression()?;
                let step = if self.peek(0)? == Some(&Token::Comma) {
                    self.expect_next(Token::Comma)?;
                    Some(self.parse_expression()?)
                } else {
                    None
                };

                self.expect_next(Token::Do)?;
                let block = self.parse_block()?;
                self.expect_next(Token::End)?;

                Ok(ForStatement::Numeric {
                    name,
                    initial,
                    limit,
                    step,
                    block,
                })
            }
            Some(&Token::Comma) | Some(&Token::In) => {
                let mut names = Vec::new();
                names.push(name);
                while self.peek(0)? == Some(&Token::Comma) {
                    self.expect_next(Token::Comma)?;
                    names.push(self.expect_identifier()?);
                }

                self.expect_next(Token::In)?;
                let values = self.parse_expression_list()?;

                self.expect_next(Token::Do)?;
                let block = self.parse_block()?;
                self.expect_next(Token::End)?;

                Ok(ForStatement::Generic {
                    names,
                    values,
                    block,
                })
            }
            Some(token) => Err(ParserError::Unexpected {
                unexpected: format!("{:?}", token),
                expected: Some("'=' ',' or 'in'".to_owned()),
            }),
            None => Err(ParserError::EndOfStream {
                expected: Some("'=' ',' or 'in'".to_owned()),
            }),
        }
    }

    /// The function statement syntax sugar simplifies function definition:
    ///
    /// ```lua
    /// statement ::= function funcname funcbody
    /// funcname ::= Name ('.' Name)* (':' Name)?
    /// ```
    ///
    /// For example, the statement
    ///
    /// ```lua
    /// function f() body end
    /// ```
    ///
    /// is equivalent with
    ///
    /// ```lua
    /// f = function() body end
    /// ```
    ///
    /// The statement
    ///
    /// ```lua
    /// function t.a.b.c.f () body end
    /// ```
    ///
    /// is equivalent with
    ///
    /// ```lua
    /// t.a.b.c.f = function () body end
    /// ```
    ///
    /// The colon syntax is used for defining methods, that is, functions that
    /// have an implicit extra parameter self. Thus, the statement
    ///
    /// ```lua
    /// function t.a.b.c:f (params) body end
    /// ```
    ///
    /// is syntactic sugar for
    ///
    /// ```lua
    /// t.a.b.c.f = function (self, params) body end
    /// ```
    pub(crate) fn parse_function_statement(&mut self) -> Result<FunctionStatement, ParserError> {
        self.expect_next(Token::Function)?;

        let name = self.expect_identifier()?;

        let mut fields = Vec::new();
        while self.peek(0)? == Some(&Token::Dot) {
            self.expect_next(Token::Dot)?;
            fields.push(self.expect_identifier()?);
        }

        let method = if self.peek(0)? == Some(&Token::Colon) {
            self.expect_next(Token::Colon)?;
            Some(self.expect_identifier()?)
        } else {
            None
        };

        let definition = self.parse_function_body()?;

        Ok(FunctionStatement {
            name,
            fields,
            method,
            definition,
        })
    }

    /// The local function statement syntax sugar simplifies function
    /// definition:
    ///
    /// ```lua
    /// local function Name funcbody
    /// ```
    ///
    /// For example, the statement
    ///
    /// ```lua
    /// local function f() body end
    /// ```
    ///
    /// is equivalent with
    ///
    /// ```lua
    /// local f; f = function () body end
    /// ```
    ///
    /// not
    ///
    /// ```lua
    /// local f = function () body end
    /// ```
    ///
    /// This only makes a difference when the body of the function contains
    /// references to f.
    pub(crate) fn parse_local_function_statement(
        &mut self,
    ) -> Result<LocalFunctionStatement, ParserError> {
        self.expect_next(Token::Local)?;
        self.expect_next(Token::Function)?;

        let name = self.expect_identifier()?;
        let definition = self.parse_function_body()?;

        Ok(LocalFunctionStatement { name, definition })
    }

    /// Local variables can be declared anywhere inside a block.
    ///
    /// The declaration can include an initial assignment:
    ///
    /// ```lua
    /// LocalDeclarationStatement ::= local namelist ('=' explist)?
    /// ```
    ///
    /// If present, an initial assignment has the same semantics of a multiple
    /// assignment. Otherwise, all variables are initialized with nil.
    pub(crate) fn parse_local_declaration_statement(
        &mut self,
    ) -> Result<LocalDeclarationStatement, ParserError> {
        self.expect_next(Token::Local)?;

        let mut names = Vec::new();
        names.push(self.expect_identifier()?);
        while self.peek(0)? == Some(&Token::Comma) {
            self.advance(1);
            names.push(self.expect_identifier()?);
        }

        let values = if self.peek(0)? == Some(&Token::Assign) {
            self.advance(1);
            self.parse_expression_list()?
        } else {
            Vec::new()
        };

        Ok(LocalDeclarationStatement { names, values })
    }
}
