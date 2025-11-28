/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ast::*;
use crate::statics::{Error, StaticsContext};
use crate::tokenizer::{Token, TokenKind, tokenize_file};
use std::rc::Rc;

pub(crate) fn parse_file(ctx: &mut StaticsContext, file_id: FileId) -> Rc<FileAst> {
    let mut items: Vec<Rc<Item>> = vec![];

    let tokens = tokenize_file(ctx, file_id);

    let mut parser = Parser::new(tokens, ctx, file_id);
    while !parser.done() {
        if let Some(item) = parser.parse_item() {
            items.push(item);
        }
    }

    let file_data = ctx.file_db.get(file_id).unwrap();
    Rc::new(FileAst {
        items,
        // remove the .abra suffix from filename
        name: file_data.nominal_path.to_str().unwrap()
            [..file_data.nominal_path.to_str().unwrap().len() - 5]
            .to_string(),
        path: file_data.full_path.clone(),
        loc: Location {
            file_id,
            lo: 0,
            hi: (file_data.source.len() - 1) as u32,
        },
        id: NodeId::new(),
    })
}

struct Parser<'a> {
    index: usize,
    tokens: Vec<Token>,

    ctx: &'a mut StaticsContext,
    file_id: FileId,
}

impl<'a> Parser<'a> {
    fn new(tokens: Vec<Token>, ctx: &'a mut StaticsContext, file_id: FileId) -> Self {
        Parser {
            index: 0,
            tokens,
            ctx,
            file_id,
        }
    }

    fn done(&self) -> bool {
        self.index >= self.tokens.len()
    }

    fn current_token(&self) -> Token {
        self.tokens[self.index].clone()
    }

    fn location(&self, begin: usize) -> Location {
        Location {
            file_id: self.file_id,
            lo: begin as u32,
            hi: self.index as u32,
        }
    }

    fn parse_item(&mut self) -> Option<Rc<Item>> {
        let current = self.current_token();
        let lo = self.index;
        Some(Rc::new(match current.kind {
            TokenKind::Fn => {
                let func_def = self.parse_func_def()?;
                Item {
                    kind: ItemKind::FuncDef(func_def).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                self.ctx.errors.push(Error::UnexpectedToken(
                    self.file_id,
                    "statement".into(),
                    current.span,
                ));
                self.index += 1;
                return None;
            }
        }))
    }

    fn parse_func_def(&mut self) -> Option<Rc<FuncDef>> {
        let current = self.current_token();
        self.ctx.errors.push(Error::UnexpectedToken(
            self.file_id,
            "function definition".into(),
            current.span,
        ));
        self.index += 1;
        return None;
    }
}
