use std::io;

use super::{
    BinaryOperator, Block, Expression, FunctionDefinition, Parser, ParserError, Suffix,
    SuffixedExpression, UnaryOperator,
};
use crate::lexer::Token;

/// Lua supports an almost conventional set of statements, similar to those in
/// Pascal or C. This set includes assignments, control structures, function
/// calls, and variable declarations.
#[derive(Debug, PartialEq)]
pub enum Statement {
    Assignment(AssignmentStatement),
    FunctionCall(FunctionCallStatement),
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
pub struct FunctionCallStatement {
    pub call: SuffixedExpression,
}

#[derive(Debug, PartialEq)]
pub struct AssignmentStatement {
    pub targets: Vec<Expression>,
    pub values: Vec<Expression>,
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
    pub if_then: Vec<(Expression, Block)>,
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
    /// Parses a statement.
    ///
    /// Although FunctionCall is an expression, it can also be a statement.
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

    /// Parses an expression statement.
    ///
    /// An expression statement is a function call or an assignment.
    pub(crate) fn parse_expression_statement(&mut self) -> Result<Statement, ParserError> {
        let suffixed_expression = self.parse_suffixed_expression()?;
        if self.peek(0)? == Some(&Token::Assign) || self.peek(0)? == Some(&Token::Comma) {
            let mut targets = Vec::new();
            targets.push(suffixed_expression);
            while self.peek(0)? == Some(&Token::Comma) {
                self.advance(1);
                targets.push(self.parse_suffixed_expression()?);
            }

            self.expect_next(Token::Assign)?;

            // type checks
            for t in &targets {
                match t {
                    Expression::Identifier(_) => {}
                    Expression::Suffixed(SuffixedExpression { primary, suffixes }) => {
                        assert!(!suffixes.is_empty());

                        match primary.as_ref() {
                            Expression::Identifier(_) => {}
                            _ => return Err(ParserError::AssignToExpression),
                        }

                        match suffixes.last().unwrap() {
                            Suffix::NamedField(_) | Suffix::IndexedField(_) => {}
                            _ => return Err(ParserError::AssignToExpression),
                        }
                    }
                    _ => return Err(ParserError::AssignToExpression),
                }
            }

            let values = self.parse_expression_list()?;
            Ok(Statement::Assignment(AssignmentStatement {
                targets,
                values,
            }))
        } else {
            match suffixed_expression {
                Expression::Suffixed(expr) => {
                    assert!(!expr.suffixes.is_empty());
                    match expr.suffixes.last().unwrap() {
                        Suffix::FunctionCall(_) | Suffix::MethodCall(_, _) => {
                            Ok(Statement::FunctionCall(FunctionCallStatement {
                                call: expr,
                            }))
                        }
                        _ => Err(ParserError::ExpressionNotStatement),
                    }
                }
                _ => Err(ParserError::ExpressionNotStatement),
            }
        }
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
    /// Let's transform the last `else block` to `elseif true then block`. So it
    /// can be merged into the `elseif expression then block` part.
    ///
    /// # Cautious
    ///
    /// The condition expression of a control structure can return any value.
    /// Both **false** and **nil** are considered _false_. All values different
    /// from **nil** and **false** are considered _true_ (in particular, the
    /// number 0 and the empty string are also true).
    pub(crate) fn parse_if_statement(&mut self) -> Result<IfStatement, ParserError> {
        let mut if_then = Vec::new();

        self.expect_next(Token::If)?;
        let expr = self.parse_expression()?;
        self.expect_next(Token::Then)?;
        let block = self.parse_block()?;
        if_then.push((expr, block));

        while self.peek(0)? == Some(&Token::ElseIf) {
            self.expect_next(Token::ElseIf)?;
            let expr = self.parse_expression()?;
            self.expect_next(Token::Then)?;
            let block = self.parse_block()?;
            if_then.push((expr, block));
        }

        // transform `else` to `elseif true`
        if self.peek(0)? == Some(&Token::Else) {
            self.expect_next(Token::Else)?;
            let expr = Expression::True;
            let block = self.parse_block()?;
            if_then.push((expr, block));
        }

        self.expect_next(Token::End)?;

        Ok(IfStatement { if_then })
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

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! id {
        ($name:expr) => {
            Expression::Identifier($name.to_owned())
        };
    }

    #[test]
    fn assignment() {
        let mut s: &[u8] = b"a = 10\nb = 20";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Assignment(AssignmentStatement {
                targets: vec![id!("a")],
                values: vec![Expression::Integer(10)]
            })
        );
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Assignment(AssignmentStatement {
                targets: vec![id!("b")],
                values: vec![Expression::Integer(20)],
            })
        );

        let mut s: &[u8] = b"a,b,c=1,2,3";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Assignment(AssignmentStatement {
                targets: vec![id!("a"), id!("b"), id!("c")],
                values: vec![
                    Expression::Integer(1),
                    Expression::Integer(2),
                    Expression::Integer(3)
                ],
            })
        );

        let mut s: &[u8] = b"f(1) = 10";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap_err(),
            ParserError::AssignToExpression
        );

        let mut s: &[u8] = b"a + b = 10";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap_err(),
            ParserError::ExpressionNotStatement
        );
    }

    #[test]
    fn function_call() {
        let mut s: &[u8] = br#"f(1, "string")"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::FunctionCall(FunctionCallStatement {
                call: SuffixedExpression {
                    primary: Box::new(id!("f")),
                    suffixes: vec![Suffix::FunctionCall(vec![
                        Expression::Integer(1),
                        Expression::String("string".to_owned())
                    ])],
                }
            })
        );
    }

    #[test]
    fn label_goto() {
        let mut s: &[u8] = b"::label:: goto label";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Label("label".to_owned())
        );
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Goto("label".to_owned())
        );
    }

    #[test]
    fn do_block() {
        let mut s: &[u8] = b"do a=10 end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Do(Block {
                stmts: vec![Statement::Assignment(AssignmentStatement {
                    targets: vec![id!("a")],
                    values: vec![Expression::Integer(10)],
                })],
                retstmt: None,
            })
        );
    }

    #[test]
    fn while_loop() {
        let mut s: &[u8] = b"while true do a=10 end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::While(WhileStatement {
                condition: Expression::True,
                block: Block {
                    stmts: vec![Statement::Assignment(AssignmentStatement {
                        targets: vec![id!("a")],
                        values: vec![Expression::Integer(10)]
                    })],
                    retstmt: None,
                }
            })
        )
    }

    #[test]
    fn repeat_loop() {
        let mut s: &[u8] = b"repeat until a~=0";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Repeat(RepeatStatement {
                block: Block {
                    stmts: vec![],
                    retstmt: None,
                },
                until: Expression::BinaryOperator(
                    BinaryOperator::NotEqual,
                    Box::new(id!("a")),
                    Box::new(Expression::Integer(0))
                )
            })
        );
    }

    #[test]
    fn for_numeric_loop() {
        let mut s: &[u8] = b"for i=0,10,1 do a=10 end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::For(ForStatement::Numeric {
                name: "i".to_owned(),
                initial: Expression::Integer(0),
                limit: Expression::Integer(10),
                step: Some(Expression::Integer(1)),
                block: Block {
                    stmts: vec![Statement::Assignment(AssignmentStatement {
                        targets: vec![id!("a")],
                        values: vec![Expression::Integer(10)],
                    })],
                    retstmt: None,
                }
            })
        );
    }

    #[test]
    fn for_generic_loop() {
        let mut s: &[u8] = br#"
function test_iterator()
    local function inc(s, c)
        if c == 10 then
            return nil
        else
            return c + 1, c + 11
        end
    end

    return inc, nil, 0
end

local sum = 0
for i in test_iterator() do
    sum = sum + i
end
"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Function(FunctionStatement {
                name: "test_iterator".to_owned(),
                fields: vec![],
                method: None,
                definition: FunctionDefinition {
                    parameters: vec![],
                    has_varargs: false,
                    body: Block {
                        stmts: vec![Statement::LocalFunction(LocalFunctionStatement {
                            name: "inc".to_owned(),
                            definition: FunctionDefinition {
                                parameters: vec!["s".to_owned(), "c".to_owned()],
                                has_varargs: false,
                                body: Block {
                                    stmts: vec![Statement::If(IfStatement {
                                        if_then: vec![
                                            (
                                                Expression::BinaryOperator(
                                                    BinaryOperator::Equal,
                                                    Box::new(id!("c")),
                                                    Box::new(Expression::Integer(10))
                                                ),
                                                Block {
                                                    stmts: vec![],
                                                    retstmt: Some(ReturnStatement {
                                                        returns: vec![Expression::Nil]
                                                    })
                                                }
                                            ),
                                            (
                                                Expression::True,
                                                Block {
                                                    stmts: vec![],
                                                    retstmt: Some(ReturnStatement {
                                                        returns: vec![
                                                            Expression::BinaryOperator(
                                                                BinaryOperator::Add,
                                                                Box::new(id!("c")),
                                                                Box::new(Expression::Integer(1))
                                                            ),
                                                            Expression::BinaryOperator(
                                                                BinaryOperator::Add,
                                                                Box::new(id!("c")),
                                                                Box::new(Expression::Integer(11))
                                                            )
                                                        ]
                                                    })
                                                }
                                            )
                                        ]
                                    })],
                                    retstmt: None,
                                }
                            }
                        })],
                        retstmt: Some(ReturnStatement {
                            returns: vec![id!("inc"), Expression::Nil, Expression::Integer(0)]
                        })
                    }
                }
            })
        );

        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::LocalDeclaration(LocalDeclarationStatement {
                names: vec!["sum".to_owned()],
                values: vec![Expression::Integer(0)]
            })
        );

        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::For(ForStatement::Generic {
                names: vec!["i".to_owned()],
                values: vec![Expression::Suffixed(SuffixedExpression {
                    primary: Box::new(id!("test_iterator")),
                    suffixes: vec![Suffix::FunctionCall(vec![])]
                })],
                block: Block {
                    stmts: vec![Statement::Assignment(AssignmentStatement {
                        targets: vec![id!("sum")],
                        values: vec![Expression::BinaryOperator(
                            BinaryOperator::Add,
                            Box::new(id!("sum")),
                            Box::new(id!("i"))
                        )],
                    })],
                    retstmt: None,
                }
            })
        );
    }

    #[test]
    fn if_stmt() {
        let mut s: &[u8] = b"if true then else end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::If(IfStatement {
                if_then: vec![
                    (
                        Expression::True,
                        Block {
                            stmts: vec![],
                            retstmt: None
                        }
                    ),
                    (
                        Expression::True,
                        Block {
                            stmts: vec![],
                            retstmt: None
                        }
                    )
                ],
            })
        );

        let mut s: &[u8] = b"if false then elseif false then end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::If(IfStatement {
                if_then: vec![
                    (
                        Expression::False,
                        Block {
                            stmts: vec![],
                            retstmt: None
                        }
                    ),
                    (
                        Expression::False,
                        Block {
                            stmts: vec![],
                            retstmt: None
                        }
                    )
                ]
            })
        );

        let mut s: &[u8] = b"if true then elseif false then else end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::If(IfStatement {
                if_then: vec![
                    (
                        Expression::True,
                        Block {
                            stmts: vec![],
                            retstmt: None,
                        }
                    ),
                    (
                        Expression::False,
                        Block {
                            stmts: vec![],
                            retstmt: None
                        }
                    ),
                    (
                        Expression::True,
                        Block {
                            stmts: vec![],
                            retstmt: None,
                        }
                    )
                ]
            })
        );
    }

    #[test]
    fn function() {
        let mut s: &[u8] = br#"function one() return 1 end
                               function add1(x) return x+1 end
                               function t.a.b.c:f() end"#;
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Function(FunctionStatement {
                name: "one".to_owned(),
                fields: vec![],
                method: None,
                definition: FunctionDefinition {
                    parameters: vec![],
                    has_varargs: false,
                    body: Block {
                        stmts: vec![],
                        retstmt: Some(ReturnStatement {
                            returns: vec![Expression::Integer(1)]
                        })
                    }
                }
            })
        );
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Function(FunctionStatement {
                name: "add1".to_owned(),
                fields: vec![],
                method: None,
                definition: FunctionDefinition {
                    parameters: vec!["x".to_owned()],
                    has_varargs: false,
                    body: Block {
                        stmts: vec![],
                        retstmt: Some(ReturnStatement {
                            returns: vec![Expression::BinaryOperator(
                                BinaryOperator::Add,
                                Box::new(id!("x")),
                                Box::new(Expression::Integer(1))
                            )]
                        })
                    }
                }
            })
        );
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Function(FunctionStatement {
                name: "t".to_owned(),
                fields: vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
                method: Some("f".to_owned()),
                definition: FunctionDefinition {
                    parameters: vec![],
                    has_varargs: false,
                    body: Block {
                        stmts: vec![],
                        retstmt: None,
                    }
                }
            })
        );
    }

    #[test]
    fn local_function() {
        let mut s: &[u8] = b"local function one() return 1 end";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::LocalFunction(LocalFunctionStatement {
                name: "one".to_owned(),
                definition: FunctionDefinition {
                    parameters: vec![],
                    has_varargs: false,
                    body: Block {
                        stmts: vec![],
                        retstmt: Some(ReturnStatement {
                            returns: vec![Expression::Integer(1)]
                        })
                    }
                }
            })
        );
    }

    #[test]
    fn local_declaration() {
        let mut s: &[u8] = b"local a, b, c = 10, 20";
        let mut parser = Parser::new(&mut s);
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::LocalDeclaration(LocalDeclarationStatement {
                names: vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
                values: vec![Expression::Integer(10), Expression::Integer(20)]
            })
        );
    }
}
