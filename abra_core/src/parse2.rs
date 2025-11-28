/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ast::*;
use crate::statics::{Error, StaticsContext};
use crate::tokenizer::{Token, TokenKind, TokenTag, tokenize_file};
use std::rc::Rc;
use strum::IntoDiscriminant;

pub(crate) fn parse_file(ctx: &mut StaticsContext, file_id: FileId) -> Rc<FileAst> {
    let mut items: Vec<Rc<Item>> = vec![];

    let tokens = tokenize_file(ctx, file_id);
    // for (i, token) in tokens.iter().enumerate() {
    //     print!("{}", token);
    //     if i < tokens.len() - 1 {
    //         print!(" ");
    //     }
    //
    // }
    // println!();
    // let Some(file_ast) = parse2::parse_or_err(ctx, file_id, file_data) else { continue; };

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

    fn current_token(&mut self) -> Option<Token> {
        match self.tokens.get(self.index) {
            Some(t) => Some(t.clone()),
            None => {
                self.ctx.errors.push(Error::RanOutOfTokens(self.file_id));
                None
            }
        }
    }

    fn expect_token(&mut self, kind: TokenTag) -> Option<()> {
        let current = self.current_token()?;
        self.index += 1;
        if current.kind.discriminant() == kind {
            Some(())
        } else {
            self.ctx.errors.push(Error::UnexpectedToken(
                self.file_id,
                "???".into(), // TODO: replace ??? with more context. what was being parsed
                current.span,
            ));
            None
        }
    }

    fn consume_token(&mut self) {
        self.index += 1;
    }

    fn expect_ident(&mut self) -> Option<Rc<Identifier>> {
        let current = self.current_token()?;
        self.index += 1;
        if let TokenKind::Ident(v) = current.kind {
            Some(Rc::new(Identifier {
                v,
                loc: Location {
                    file_id: self.file_id,
                    lo: current.span.lo as u32,
                    hi: current.span.hi as u32,
                }, // TODO: these conversions are annoying just use usize until it becomes a problem
                id: NodeId::new(),
            }))
        } else {
            self.ctx.errors.push(Error::UnexpectedToken(
                self.file_id,
                "???".into(), // TODO: replace ??? with more context. what was being parsed. What kind of token was being expected? Maybe make a separate error type. An identifier was being expected
                current.span,
            ));
            None
        }
    }

    fn skip_newlines(&mut self) {
        while let Some(tok) = self.current_token()
            && tok.kind == TokenKind::Newline
        {
            self.index += 1;
        }
    }

    fn location(&mut self, begin: usize) -> Location {
        Location {
            file_id: self.file_id,
            lo: begin as u32,
            hi: self.current_token().unwrap().span.hi as u32,
        }
    }

    fn parse_item(&mut self) -> Option<Rc<Item>> {
        self.skip_newlines();
        let current = self.current_token()?;
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
        self.expect_token(TokenTag::Fn)?;
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::OpenParen)?;
        // todo get function args
        let mut args = vec![];
        while !matches!(self.current_token()?.kind, TokenKind::CloseParen) {
            let name = self.expect_ident()?;
            args.push((name, None)); // TODO: parse annotation
            if matches!(self.current_token()?.kind, TokenKind::Comma) {
                self.consume_token();
            }
        }
        self.expect_token(TokenTag::CloseParen)?;
        // todo get optional return type
        let ret_type = None;
        self.expect_token(TokenTag::Eq)?;
        let body = self.parse_expr()?;

        Some(Rc::new(FuncDef {
            name,
            args,
            ret_type,
            body,
        }))
    }

    fn parse_expr(&mut self) -> Option<Rc<Expr>> {
        // self.skip_newlines();
        let current = self.current_token()?;
        let lo = self.index;
        Some(Rc::new(match current.kind {
            TokenKind::Match => {
                self.expect_token(TokenTag::Match)?;
                let scrutiny = self.parse_expr()?;
                let mut arms: Vec<Rc<MatchArm>> = vec![];
                while !matches!(self.current_token()?.kind, TokenKind::CloseBrace) {
                    arms.push(self.parse_match_arm()?);
                }
                self.expect_token(TokenTag::CloseBrace)?;
                Expr {
                    kind: Rc::new(ExprKind::Match(scrutiny, arms)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                self.ctx.errors.push(Error::UnexpectedToken(
                    self.file_id,
                    "expression".into(),
                    current.span,
                ));
                self.index += 1;
                return None;
            }
        }))
    }

    fn parse_match_arm(&mut self) -> Option<Rc<MatchArm>> {
        let lo = self.index;

        let pat = self.parse_match_pattern()?;
        let stmt = self.parse_stmt()?;
        Some(Rc::new(MatchArm {
            pat,
            stmt,
            loc: self.location(lo),
            id: NodeId::new(),
        }))
    }

    fn parse_match_pattern(&mut self) -> Option<Rc<Pat>> {
        let lo = self.index;

        panic!();
    }

    fn parse_stmt(&mut self) -> Option<Rc<Stmt>> {
        let lo = self.index;

        panic!();
    }
}
