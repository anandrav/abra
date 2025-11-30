/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ast::*;
use crate::statics::{Error, StaticsContext};
use crate::tokenizer::{Span, Token, TokenKind, TokenTag, tokenize_file};
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

    let mut parser = Parser::new(tokens, file_id);
    let mut clean = true;
    while !parser.done() {
        let before = parser.index;
        match parser.parse_item() {
            Ok(item) => {
                items.push(item);
                clean = true
            }
            Err(e) => {
                // if clean {
                ctx.errors.push(*e);
                clean = false;
                // }
                if parser.index == before {
                    parser.index += 1;
                }
            }
        }
    }
    ctx.errors.extend(parser.errors);

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
            hi: (file_data.source.len() - 1),
        },
        id: NodeId::new(),
    })
}

struct Parser {
    index: usize,
    tokens: Vec<Token>,

    file_id: FileId,
    errors: Vec<Error>,
}

impl Parser {
    fn new(tokens: Vec<Token>, file_id: FileId) -> Self {
        Parser {
            index: 0,
            tokens,
            file_id,
            errors: vec![],
        }
    }

    fn done(&mut self) -> bool {
        self.skip_newlines();
        self.current_token().kind == TokenKind::Eof // TODO: instead of using kind in some places and tag other places, just use tag everywhere. Add a .tag() method to get the tag
    }

    fn current_token(&self) -> Token {
        match self.tokens.get(self.index) {
            Some(t) => t.clone(),
            None => Token {
                kind: TokenKind::Eof,
                span: Span { lo: 0, hi: 0 },
            }, // TODO: fix span of Eof
        }
    }

    fn expect_token(&mut self, kind: TokenTag) {
        if kind != TokenTag::Newline {
            self.skip_newlines();
        }
        let current = self.current_token();
        if current.kind.discriminant() == kind {
            self.index += 1;
        } else {
            self.errors.push(Error::UnexpectedToken(
                self.file_id,
                kind.to_string(),
                current.kind.discriminant().to_string(),
                current.span,
            ))
        }
    }

    fn consume_token(&mut self) {
        self.index += 1;
    }

    fn expect_ident(&mut self) -> Result<Rc<Identifier>, Box<Error>> {
        let current = self.current_token();
        self.index += 1;
        if let TokenKind::Ident(v) = current.kind {
            Ok(Rc::new(Identifier {
                v,
                loc: Location {
                    file_id: self.file_id,
                    lo: current.span.lo,
                    hi: current.span.hi,
                },
                id: NodeId::new(),
            }))
        } else {
            Err(Error::UnexpectedToken(
                self.file_id,
                "identifier".into(),
                current.kind.discriminant().to_string(),
                current.span,
            )
            .into())
        }
    }

    fn skip_newlines(&mut self) {
        while self.current_token().kind == TokenKind::Newline {
            self.index += 1;
        }
    }

    fn location(&mut self, begin: usize) -> Location {
        Location {
            file_id: self.file_id,
            lo: begin,
            hi: self.current_token().span.hi,
        }
    }

    fn parse_item(&mut self) -> Result<Rc<Item>, Box<Error>> {
        self.skip_newlines();
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Fn => {
                let func_def = self.parse_func_def()?;
                Item {
                    kind: ItemKind::FuncDef(func_def).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                let stmt = self.parse_stmt()?;
                Item {
                    kind: ItemKind::Stmt(stmt).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
        }))
    }

    fn parse_func_def(&mut self) -> Result<Rc<FuncDef>, Box<Error>> {
        self.expect_token(TokenTag::Fn);
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::OpenParen);
        // todo get function args
        let mut args = vec![];
        while !matches!(self.current_token().kind, TokenKind::CloseParen) {
            let name = self.expect_ident()?;
            args.push((name, None)); // TODO: parse annotation
            if self.current_token().kind == TokenKind::Comma {
                self.consume_token();
            } else {
                break;
            }
        }
        self.expect_token(TokenTag::CloseParen);
        // todo get optional return type
        let ret_type = None;
        if self.current_token().kind == TokenKind::Eq {
            self.expect_token(TokenTag::Eq); // TODO: support the other syntax for func def
            let body = self.parse_expr()?;

            Ok(Rc::new(FuncDef {
                name,
                args,
                ret_type,
                body,
            }))
        } else {
            let block_start = self.index;
            let statements = self.parse_statement_block()?;
            let block_expr = Expr {
                kind: ExprKind::Block(statements).into(),
                loc: self.location(block_start),
                id: NodeId::new(),
            }
            .into();
            Ok(Rc::new(FuncDef {
                name,
                args,
                ret_type,
                body: block_expr,
            }))
        }
    }

    fn parse_statement_block(&mut self) -> Result<Vec<Rc<Stmt>>, Box<Error>> {
        self.expect_token(TokenTag::OpenBrace);
        let mut statements: Vec<Rc<Stmt>> = vec![];
        while !matches!(self.current_token().kind, TokenKind::CloseBrace) {
            statements.push(self.parse_stmt()?);
            if self.current_token().kind == TokenKind::Newline {
                self.consume_token();
            } else {
                break;
            }
        }
        self.expect_token(TokenTag::CloseBrace);
        Ok(statements)
    }

    fn parse_expr(&mut self) -> Result<Rc<Expr>, Box<Error>> {
        let ret = self.parse_expr_bp(0)?;
        Ok(ret)
    }

    fn parse_expr_bp(&mut self, binding_power: u8) -> Result<Rc<Expr>, Box<Error>> {
        let lo = self.current_token().span.lo;

        // pratt
        let mut lhs = self.parse_expr_term()?;
        loop {
            // postfix operators/expressions
            if let Some(op) = self.parse_postfix_op() {
                if op.precedence() <= binding_power {
                    break;
                }

                self.consume_token(); // TODO: consume the token in handle_postfix_expr(). Use expect_token instead to be sure
                self.handle_postfix_expr(&mut lhs, lo, op)?;
                continue;
            }

            // binary operators
            let Some(op) = self.parse_binop() else {
                return Ok(lhs);
            };
            if op.precedence() <= binding_power {
                // *** Looping for weaker operators and left-associativity ***
                // since this op is lower precedence, the caller must make
                // a tree first. Then the caller will loop again and handle
                // the operator.
                break;
            }

            // *** Recursion for stronger operators and right-associativity ***
            // since op is a higher precedence than what was encountered before,
            // make a tree with this operator. The operator is lower height in the
            // syntax tree since it is stronger
            self.consume_token();
            let rhs = self.parse_expr_bp(op.precedence())?;
            lhs = Rc::new(Expr {
                kind: ExprKind::BinOp(lhs, op, rhs).into(),
                loc: self.location(lo),
                id: NodeId::new(),
            });
        }

        Ok(lhs)
    }

    fn handle_postfix_expr(
        &mut self,
        lhs: &mut Rc<Expr>,
        lo: usize,
        op: PostfixOp,
    ) -> Result<(), Box<Error>> {
        match op {
            PostfixOp::FuncCall => {
                let mut args: Vec<Rc<Expr>> = vec![];
                while !matches!(self.current_token().kind, TokenKind::CloseParen) {
                    args.push(self.parse_expr()?);
                    if self.current_token().kind == TokenKind::Comma {
                        self.consume_token();
                    } else {
                        break;
                    }
                }
                self.expect_token(TokenTag::CloseParen);
                *lhs = Rc::new(Expr {
                    kind: ExprKind::FuncAp(lhs.clone(), args).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                })
            }
            PostfixOp::MemberAccess => {
                let ident = self.expect_ident()?;
                if self.current_token().kind == TokenKind::OpenParen {
                    // member func call
                    // `my_struct.my_member_func(`
                    // TODO: code duplication. Make helper function for getting args
                    let mut args: Vec<Rc<Expr>> = vec![];
                    while !matches!(self.current_token().kind, TokenKind::CloseParen) {
                        args.push(self.parse_expr()?);
                        if self.current_token().kind == TokenKind::Comma {
                            self.consume_token();
                        } else {
                            break;
                        }
                    }
                    self.expect_token(TokenTag::CloseParen);
                    *lhs = Rc::new(Expr {
                        kind: ExprKind::MemberFuncAp(Some(lhs.clone()), ident, args).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    })
                } else {
                    // member access
                    // `my_struct.my_field`
                    *lhs = Rc::new(Expr {
                        kind: ExprKind::MemberAccess(lhs.clone(), ident).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    })
                }
            }
            PostfixOp::IndexAccess => {
                let index = self.parse_expr()?;
                self.expect_token(TokenTag::CloseBracket);
                *lhs = Rc::new(Expr {
                    kind: ExprKind::IndexAccess(lhs.clone(), index).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                })
            }
            PostfixOp::Unwrap => {
                *lhs = Rc::new(Expr {
                    kind: ExprKind::Unwrap(lhs.clone()).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                })
            }
        }
        Ok(())
    }

    fn parse_binop(&mut self) -> Option<BinaryOperator> {
        Some(match self.current_token().kind {
            TokenKind::Plus => BinaryOperator::Add,
            TokenKind::Minus => BinaryOperator::Subtract,
            TokenKind::Star => BinaryOperator::Multiply,
            TokenKind::Slash => BinaryOperator::Divide,
            TokenKind::EqEq => BinaryOperator::Equal,
            TokenKind::Lt => BinaryOperator::LessThan,
            TokenKind::Le => BinaryOperator::LessThanOrEqual,
            TokenKind::Gt => BinaryOperator::GreaterThan,
            TokenKind::Ge => BinaryOperator::GreaterThanOrEqual,
            TokenKind::Mod => BinaryOperator::Mod,
            TokenKind::Caret => BinaryOperator::Pow,
            TokenKind::DotDot => BinaryOperator::Format,
            TokenKind::And => BinaryOperator::And,
            TokenKind::Or => BinaryOperator::Or,
            _ => return None,
        })
    }

    fn parse_postfix_op(&mut self) -> Option<PostfixOp> {
        Some(match self.current_token().kind {
            TokenKind::OpenParen => PostfixOp::FuncCall,
            TokenKind::Dot => PostfixOp::MemberAccess,
            TokenKind::OpenBracket => PostfixOp::IndexAccess,
            TokenKind::Bang => PostfixOp::Unwrap,
            _ => return None,
        })
    }

    fn parse_expr_term(&mut self) -> Result<Rc<Expr>, Box<Error>> {
        // self.skip_newlines();
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Ident(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Variable(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Int(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Int(s.parse::<i64>().unwrap())), // TODO: don't unwrap. report error if this can't fit in an i64
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::String(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Str(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Match => {
                self.expect_token(TokenTag::Match);
                let scrutiny = self.parse_expr()?;
                self.expect_token(TokenTag::OpenBrace);
                let mut arms: Vec<Rc<MatchArm>> = vec![];
                self.skip_newlines();
                let mut clean = true;
                while !matches!(self.current_token().kind, TokenKind::CloseBrace) {
                    arms.push(self.parse_match_arm()?);
                    // let checkpoint = self.index;
                    // match self.parse_match_arm() {
                    //     Ok(arm) => {
                    //         clean = true;
                    //         arms.push(arm)
                    //     }
                    //     Err(e) => {
                    //         self.errors.push(e);
                    //         if clean {
                    //             clean = false;
                    //             continue;
                    //         } else {
                    //             self.index = checkpoint;
                    //             break;
                    //         }
                    //     }
                    // }
                    if self.current_token().kind == TokenKind::Newline {
                        self.skip_newlines();
                    } else {
                        break;
                    }
                }
                self.expect_token(TokenTag::CloseBrace);
                Expr {
                    kind: Rc::new(ExprKind::Match(scrutiny, arms)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    self.file_id,
                    "expression term".into(),
                    current.kind.discriminant().to_string(),
                    current.span,
                )
                .into());
            }
        }))
    }

    fn parse_match_arm(&mut self) -> Result<Rc<MatchArm>, Box<Error>> {
        // self.skip_newlines();
        let lo = self.current_token().span.lo;

        let pat = self.parse_match_pattern()?;
        self.expect_token(TokenTag::RArrow);
        let stmt = self.parse_stmt()?;
        Ok(Rc::new(MatchArm {
            pat,
            stmt,
            loc: self.location(lo),
            id: NodeId::new(),
        }))
    }

    fn parse_match_pattern(&mut self) -> Result<Rc<Pat>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Ident(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Binding(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Int(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Int(s.parse::<i64>().unwrap())), // TODO: don't unwrap. report error if this can't fit in an i64
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    self.file_id,
                    "match arm pattern".into(),
                    current.kind.discriminant().to_string(),
                    current.span,
                )
                .into());
            }
        }))
    }

    fn parse_let_pattern(&mut self) -> Result<Rc<Pat>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Ident(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Binding(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    self.file_id,
                    "pattern".into(),
                    current.kind.discriminant().to_string(),
                    current.span,
                )
                .into());
            }
        }))
    }

    fn parse_let_pattern_annotated(&mut self) -> Result<PatAnnotated, Box<Error>> {
        let lo = self.current_token().span.lo;

        let pat = self.parse_let_pattern()?;
        if self.current_token().kind == TokenKind::Colon {
            let annot = self.parse_typ()?;
            Ok((pat, Some(annot)))
        } else {
            Ok((pat, None))
        }
    }

    fn parse_typ(&mut self) -> Result<Rc<Type>, Box<Error>> {
        todo!()
        // let current = self.current_token();
        // let lo = self.current_token().span.lo;
        // Ok(Rc::new(match current.kind {
        //     TokenKind::Ident(s) => {
        //         self.consume_token();
        //         Expr {
        //             kind: Rc::new(ExprKind::Variable(s)),
        //             loc: self.location(lo),
        //             id: NodeId::new(),
        //         }
        //     }
        //     TokenKind::Int(s) => {
        //         self.consume_token();
        //         Expr {
        //             kind: Rc::new(ExprKind::Int(s.parse::<i64>().unwrap())), // TODO: don't unwrap. report error if this can't fit in an i64
        //             loc: self.location(lo),
        //             id: NodeId::new(),
        //         }
        //     }
        //     TokenKind::String(s) => {
        //         self.consume_token();
        //         Expr {
        //             kind: Rc::new(ExprKind::Str(s)),
        //             loc: self.location(lo),
        //             id: NodeId::new(),
        //         }
        //     }
        //     TokenKind::Match => {
        //         self.expect_token(TokenTag::Match);
        //         let scrutiny = self.parse_expr()?;
        //         self.expect_token(TokenTag::OpenBrace);
        //         let mut arms: Vec<Rc<MatchArm>> = vec![];
        //         self.skip_newlines();
        //         let mut clean = true;
        //         while !matches!(self.current_token().kind, TokenKind::CloseBrace) {
        //             arms.push(self.parse_match_arm()?);
        //             // let checkpoint = self.index;
        //             // match self.parse_match_arm() {
        //             //     Ok(arm) => {
        //             //         clean = true;
        //             //         arms.push(arm)
        //             //     }
        //             //     Err(e) => {
        //             //         self.errors.push(e);
        //             //         if clean {
        //             //             clean = false;
        //             //             continue;
        //             //         } else {
        //             //             self.index = checkpoint;
        //             //             break;
        //             //         }
        //             //     }
        //             // }
        //             if self.current_token().kind == TokenKind::Newline {
        //                 self.skip_newlines();
        //             } else {
        //                 break;
        //             }
        //         }
        //         self.expect_token(TokenTag::CloseBrace);
        //         Expr {
        //             kind: Rc::new(ExprKind::Match(scrutiny, arms)),
        //             loc: self.location(lo),
        //             id: NodeId::new(),
        //         }
        //     }
        //     _ => {
        //         return Err(Error::UnexpectedToken(
        //             self.file_id,
        //             "expression term".into(),
        //             current.kind.discriminant().to_string(),
        //             current.span,
        //         )
        //             .into());
        //     }
        // }))
    }

    fn parse_stmt(&mut self) -> Result<Rc<Stmt>, Box<Error>> {
        self.skip_newlines();

        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Let => {
                self.expect_token(TokenTag::Let);
                let pat = self.parse_let_pattern_annotated()?;
                self.expect_token(TokenTag::Eq);
                let expr = self.parse_expr()?;
                Stmt {
                    kind: StmtKind::Let(false, pat, expr).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
                .into()
            }
            TokenKind::Var => {
                self.expect_token(TokenTag::Var);
                let pat = self.parse_let_pattern_annotated()?;
                self.expect_token(TokenTag::Eq);
                let expr = self.parse_expr()?;
                Stmt {
                    kind: StmtKind::Let(true, pat, expr).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
                .into()
            }
            TokenKind::Break => Stmt {
                kind: StmtKind::Break.into(),
                loc: self.location(lo),
                id: NodeId::new(),
            }
            .into(),
            TokenKind::Continue => Stmt {
                kind: StmtKind::Continue.into(),
                loc: self.location(lo),
                id: NodeId::new(),
            }
            .into(),
            TokenKind::Return => {
                self.expect_token(TokenTag::Return);
                let expr = self.parse_expr()?;
                Stmt {
                    kind: StmtKind::Return(expr).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::While => {
                self.expect_token(TokenTag::While);
                let cond = self.parse_expr()?;
                let statements = self.parse_statement_block()?;

                Stmt {
                    kind: StmtKind::WhileLoop(cond, statements).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::For => {
                self.expect_token(TokenTag::For);
                let pat = self.parse_let_pattern()?;
                self.expect_token(TokenTag::In);
                let iterable = self.parse_expr()?;
                let statements = self.parse_statement_block()?;

                Stmt {
                    kind: StmtKind::ForLoop(pat, iterable, statements).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::If => {
                self.expect_token(TokenTag::If);
                let condition = self.parse_expr()?;
                let then_start = self.index;
                let statements_then = self.parse_statement_block()?;
                if matches!(self.current_token().kind, TokenKind::Else) {
                    let then_block = Expr {
                        kind: Rc::new(ExprKind::Block(statements_then)),
                        loc: self.location(then_start),
                        id: NodeId::new(),
                    }
                    .into();

                    let else_start = self.index;
                    let statements_else = self.parse_statement_block()?;
                    let else_block = Expr {
                        kind: Rc::new(ExprKind::Block(statements_else)),
                        loc: self.location(else_start),
                        id: NodeId::new(),
                    }
                    .into();

                    let expr = Expr {
                        kind: Rc::new(ExprKind::IfElse(condition, then_block, else_block)),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                    .into();
                    Stmt {
                        kind: StmtKind::Expr(expr).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                } else {
                    Stmt {
                        kind: StmtKind::If(condition, statements_then).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            _ => {
                let expr = self.parse_expr()?;
                if self.current_token().kind == TokenKind::Eq {
                    self.expect_token(TokenTag::Eq);
                    let rhs = self.parse_expr()?;
                    Stmt {
                        kind: StmtKind::Set(expr, rhs).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                } else {
                    Stmt {
                        kind: StmtKind::Expr(expr).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
        }))
    }
}

enum PostfixOp {
    MemberAccess,
    IndexAccess,
    FuncCall,
    Unwrap,
}

impl PostfixOp {
    fn precedence(&self) -> u8 {
        match self {
            PostfixOp::MemberAccess => 10,
            PostfixOp::IndexAccess => 11,
            PostfixOp::FuncCall => 12,
            PostfixOp::Unwrap => 13,
        }
    }
}
