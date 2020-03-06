use std::io;

use super::{Parser, ParserError, ReturnStatement, Statement};
use crate::lexer::Token;

/// A block is a list of statements, which are executed sequentially:
///
/// Block := { Statement }
///
/// Lua has empty statements that allow you to separate statements with
/// semicolons, start a block with a semicolon or write two semicolons in
/// sequence:
///
/// Statement := ';'
///
/// A block can be explicitly delimited to produce a single statement:
///
/// Statement := **do** Block **end**
///
/// Explicit blocks are useful to control the scope of variable declarations.
/// Explicit blocks are also sometimes used to add a return statement in the
/// middle of another block.
#[derive(Debug, PartialEq)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub retstmt: Option<ReturnStatement>,
}

impl<'a, S: io::Read> Parser<'a, S> {
    /// Parses a block.
    ///
    /// A block can be in the following structures:
    ///
    /// 1. **while** expression **do** block **end**
    /// 2. **repeat** block **until** expression
    /// 3. **if** expression **then** block **else** block **end**
    /// 4. **if** expression **then** block **elseif** expression **then** block **end**
    /// 5. **do** block **end** in **for**loop or standalone
    /// 6. and function body
    ///
    /// where the bold are keyworkds.
    pub(crate) fn parse_block(&mut self) -> Result<Block, ParserError> {
        let mut stmts = Vec::new();
        let mut retstmt = None;

        loop {
            match self.peek(0)? {
                Some(&Token::SemiColon) => {
                    self.advance(1);
                }
                Some(&Token::Return) => {
                    retstmt = Some(self.parse_return_statement()?);
                    break;
                }
                Some(&Token::End) | Some(&Token::Until) | Some(&Token::Else)
                | Some(&Token::ElseIf) => break,
                None => break,
                _ => {
                    stmts.push(self.parse_statement()?);
                }
            }
        }

        Ok(Block { stmts, retstmt })
    }
}
