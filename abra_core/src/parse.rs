/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ast::*;
use crate::parse::lexer::{Token, TokenKind, TokenTag, tokenize_file};
use crate::statics::{Error, StaticsContext};
pub(crate) use lexer::Span;
use std::mem;
use std::rc::Rc;
use strum::IntoDiscriminant;
mod lexer;

pub(crate) fn parse_file(ctx: &mut StaticsContext, file_id: FileId) -> Rc<FileAst> {
    let mut items: Vec<Rc<Item>> = vec![];

    let tokens = tokenize_file(ctx, file_id);

    let file_len = {
        let file_data = ctx.file_db.get(file_id).unwrap();
        file_data.source.len()
    };
    let mut parser = Parser::new(tokens, file_id, file_len);
    while !parser.done() {
        match parser.parse_item() {
            Ok(item) => {
                items.push(item);
            }
            Err(e) => {
                // flush errors
                let errs = std::mem::take(&mut parser.errors);
                if !parser.error_found {
                    // only report errors for this file once.
                    parser.error_found = true;
                    ctx.errors.extend(errs);

                    ctx.errors.push(*e);
                }
                parser.index += 1;
            }
        }
    }
    ctx.errors.extend(parser.errors);

    let file_data = ctx.file_db.get(file_id).unwrap();
    Rc::new(FileAst {
        items,
        // remove the .abra suffix from filename
        package_name: file_data.package_name.clone(),
        package_name_str: file_data.package_name.to_str().unwrap().to_string(),
        absolute_path: file_data.absolute_path.clone(),
        loc: Location {
            file_id,
            lo: 0,
            hi: file_data.source.len(),
        },
        id: NodeId::new(),
    })
}

struct Parser {
    index: usize,
    errors: Vec<Error>,
    error_found: bool,

    tokens: Vec<Token>,
    file_id: FileId,
    file_len: usize, // used for EOF tokens
}

impl Parser {
    fn new(tokens: Vec<Token>, file_id: FileId, file_len: usize) -> Self {
        Parser {
            index: 0,
            error_found: false,
            tokens,
            file_id,
            file_len,
            errors: vec![],
        }
    }

    fn done(&mut self) -> bool {
        self.skip_newlines();
        self.current_token().tag() == TokenTag::Eof
    }

    fn current_token(&self) -> Token {
        match self.tokens.get(self.index) {
            Some(t) => t.clone(),
            None => self.eof(),
        }
    }

    fn prev_token(&self) -> Token {
        match self.tokens.get(self.index - 1) {
            Some(t) => t.clone(),
            None => self.eof(),
        }
    }

    fn current_token_location(&self) -> Location {
        let current = self.current_token();
        Location {
            file_id: self.file_id,
            lo: current.span.lo,
            hi: current.span.hi,
        }
    }

    fn peek_token(&self, diff: usize) -> Token {
        match self.tokens.get(self.index + diff) {
            Some(t) => t.clone(),
            None => self.eof(),
        }
    }

    fn eof(&self) -> Token {
        Token {
            kind: TokenKind::Eof,
            span: Span {
                lo: self.file_len - 1,
                hi: self.file_len - 1,
            },
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
                kind.to_string(),
                current.kind.discriminant().to_string(),
                self.current_token_location(),
            ))
        }
    }

    fn expect_token_opt(&mut self, kind: TokenTag) {
        if kind != TokenTag::Newline {
            self.skip_newlines();
        }
        let current = self.current_token();
        if current.kind.discriminant() == kind {
            self.index += 1;
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
                "identifier".into(),
                current.kind.discriminant().to_string(),
                self.current_token_location(),
            )
            .into())
        }
    }

    fn expect_path_ident(&mut self) -> Result<Rc<Identifier>, Box<Error>> {
        let current = self.current_token();
        self.index += 1;
        if let TokenKind::Ident(v) = current.kind {
            let mut segments = vec![];
            segments.push(v);

            while self.current_token().tag() == TokenTag::Slash {
                self.consume_token();
                let TokenKind::Ident(v) = self.current_token().kind else {
                    return Err(Error::UnexpectedToken(
                        "path identifier".into(),
                        self.current_token().kind.discriminant().to_string(),
                        self.current_token_location(),
                    )
                    .into());
                };
                self.consume_token();
                segments.push(v.clone());
            }

            let joined = segments.join("/");
            Ok(Rc::new(Identifier {
                v: joined,
                loc: Location {
                    file_id: self.file_id,
                    lo: current.span.lo,
                    hi: current.span.hi,
                },
                id: NodeId::new(),
            }))
        } else {
            Err(Error::UnexpectedToken(
                "path identifier".into(),
                current.kind.discriminant().to_string(),
                self.current_token_location(),
            )
            .into())
        }
    }

    fn expect_poly_ident(&mut self) -> Result<Rc<Identifier>, Box<Error>> {
        let current = self.current_token();
        self.index += 1;
        if let TokenKind::PolyIdent(v) = current.kind {
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
                "polytype identifier".into(),
                current.kind.discriminant().to_string(),
                self.current_token_location(),
            )
            .into())
        }
    }

    fn skip_newlines(&mut self) {
        while self.current_token().tag() == TokenTag::Newline {
            self.index += 1;
        }
    }

    fn location(&mut self, begin: usize) -> Location {
        Location {
            file_id: self.file_id,
            lo: begin,
            hi: self.prev_token().span.hi,
        }
    }

    fn parse_item(&mut self) -> Result<Rc<Item>, Box<Error>> {
        self.parse_item_with_attributes(vec![])
    }

    fn parse_item_with_attributes(
        &mut self,
        mut attributes: Vec<Attribute>,
    ) -> Result<Rc<Item>, Box<Error>> {
        self.skip_newlines();
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Pound => {
                self.consume_token();
                let name = self.expect_ident()?;
                attributes.push(Attribute {
                    name,
                    _args: vec![], // TODO: parse attribute args
                });
                return self.parse_item_with_attributes(attributes);
            }
            TokenKind::Use => {
                self.consume_token();
                let ident = self.expect_path_ident()?;
                let mut import_kind: ImportKind = ImportKind::Glob;
                if self.current_token().tag() == TokenTag::Except
                    || self.current_token().tag() == TokenTag::Dot
                {
                    let exclusion = self.current_token().tag() == TokenTag::Except;
                    self.consume_token();
                    let mut list: Vec<Rc<Identifier>> = vec![];
                    if self.current_token().tag() == TokenTag::OpenParen {
                        self.expect_token(TokenTag::OpenParen);
                        list.extend(self.parse_delimited_list(
                            TokenTag::CloseParen,
                            TokenTag::Comma,
                            Self::expect_ident,
                        )?);
                    } else {
                        // single item unparenthesized
                        list.push(self.expect_ident()?);
                    }

                    if exclusion {
                        import_kind = ImportKind::Exclusion(list);
                    } else {
                        import_kind = ImportKind::Inclusion(list);
                    }
                } else if self.current_token().tag() == TokenTag::As {
                    self.consume_token();
                    let ident = self.expect_ident()?;
                    import_kind = ImportKind::As(ident);
                }
                Item {
                    kind: ItemKind::Import(ident, import_kind).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Type => {
                self.consume_token();
                let name = self.expect_ident()?;
                let mut args = vec![];
                if self.current_token().tag() == TokenTag::Lt {
                    args = self.parse_type_args()?;
                }
                self.expect_token(TokenTag::Eq);
                if self.current_token().tag() == TokenTag::OpenBrace {
                    // struct
                    let struct_def = self.parse_struct_def(name, args, attributes)?;
                    Item {
                        kind: ItemKind::TypeDef(TypeDefKind::Struct(struct_def)).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                } else {
                    // enum
                    let enum_def = self.parse_enum_def(name, args, attributes)?;
                    Item {
                        kind: ItemKind::TypeDef(TypeDefKind::Enum(enum_def)).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            TokenKind::Interface => {
                let iface_def = self.parse_iface_def(attributes)?;
                Item {
                    kind: ItemKind::InterfaceDef(iface_def).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Fn => {
                if attributes.iter().any(|a| a.is_host() || a.is_foreign()) {
                    let func_decl = self.parse_func_decl(attributes)?;
                    Item {
                        kind: ItemKind::FuncDecl(func_decl).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                } else {
                    let func_def = self.parse_func_def(attributes)?;
                    Item {
                        kind: ItemKind::FuncDef(func_def).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            TokenKind::Implement => {
                self.consume_token();
                let iface = self.expect_ident()?;
                self.expect_token(TokenTag::For);
                let typ = self.parse_type()?;
                self.expect_token(TokenTag::OpenBrace);
                let methods = self.parse_delimited_list(
                    TokenTag::CloseBrace,
                    TokenTag::Newline,
                    |parser: &mut Parser| {
                        let mut attributes = vec![];
                        while parser.current_token().tag() == TokenTag::Pound {
                            attributes.push(parser.parse_attribute()?);
                        }
                        parser.parse_func_def(attributes)
                    },
                )?;

                let interface_impl = InterfaceImpl {
                    iface,
                    typ,
                    methods,
                    id: NodeId::new(),
                }
                .into();
                Item {
                    kind: ItemKind::InterfaceImpl(interface_impl).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Extend => {
                self.consume_token();
                let typ = self.parse_type()?;
                self.expect_token(TokenTag::OpenBrace);
                let mut methods = vec![];
                // TODO: use parse_delimited_list
                while !matches!(self.current_token().tag(), TokenTag::CloseBrace) {
                    let mut attributes = vec![];
                    while self.current_token().tag() == TokenTag::Pound {
                        attributes.push(self.parse_attribute()?);
                    }
                    methods.push(self.parse_func_def(attributes)?);
                    if self.current_token().tag() == TokenTag::Newline {
                        self.consume_token();
                    } else {
                        break;
                    }
                }
                self.expect_token(TokenTag::CloseBrace);

                let extension = Extension {
                    typ,
                    methods,
                    id: NodeId::new(),
                }
                .into();
                Item {
                    kind: ItemKind::Extension(extension).into(),
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

    fn parse_attribute(&mut self) -> Result<Attribute, Box<Error>> {
        self.consume_token();
        let name = self.expect_ident()?;
        Ok(Attribute {
            name,
            _args: vec![], // TODO: parse attribute args
        })
    }

    fn parse_type_args(&mut self) -> Result<Vec<Rc<Polytype>>, Box<Error>> {
        self.expect_token(TokenTag::Lt);
        let mut args: Vec<Rc<Polytype>> = vec![];
        // TODO: use parse_delimited_list
        while !matches!(self.current_token().tag(), TokenTag::Gt) {
            self.skip_newlines();
            let name = self.expect_poly_ident()?;
            let mut interfaces: Vec<Rc<Interface>> = vec![];
            while self.current_token().tag() == TokenTag::Ident {
                interfaces.push(self.parse_interface_constraint()?);
            }
            args.push(Rc::new(Polytype { name, interfaces }));
            if self.current_token().tag() == TokenTag::Comma {
                self.consume_token();
            } else {
                break;
            }
        }
        self.expect_token(TokenTag::Gt);
        Ok(args)
    }

    fn parse_interface_constraint(&mut self) -> Result<Rc<Interface>, Box<Error>> {
        let name = self.expect_ident()?;
        let mut arguments: Vec<(Rc<Identifier>, Rc<Type>)> = vec![];
        if self.current_token().tag() == TokenTag::Lt {
            self.consume_token();
            arguments.extend(self.parse_delimited_list(
                TokenTag::Gt,
                TokenTag::Comma,
                Self::parse_interface_constraint_arg,
            )?);
        }
        Ok(Rc::new(Interface { name, arguments }))
    }

    fn parse_interface_constraint_arg(&mut self) -> Result<(Rc<Identifier>, Rc<Type>), Box<Error>> {
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::Eq);
        let val = self.parse_type()?;
        Ok((name, val))
    }

    fn parse_iface_def(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Rc<InterfaceDef>, Box<Error>> {
        self.expect_token(TokenTag::Interface);
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::OpenBrace);
        let mut methods: Vec<Rc<FuncDecl>> = vec![];
        let mut output_types: Vec<Rc<InterfaceOutputType>> = vec![];
        loop {
            self.skip_newlines();
            if self.current_token().tag() == TokenTag::Fn {
                methods.push(self.parse_func_decl(vec![])?);
            } else if self.current_token().tag() == TokenTag::OutputType {
                output_types.push(self.parse_output_type_decl()?);
            } else {
                break;
            }
        }
        self.expect_token(TokenTag::CloseBrace);
        Ok(Rc::new(InterfaceDef {
            name,
            methods,
            output_types,
            attributes,
        }))
    }

    fn parse_struct_def(
        &mut self,
        name: Rc<Identifier>,
        ty_args: Vec<Rc<Polytype>>,
        attributes: Vec<Attribute>,
    ) -> Result<Rc<StructDef>, Box<Error>> {
        self.expect_token(TokenTag::OpenBrace);
        let fields = self.parse_delimited_list(
            TokenTag::CloseBrace,
            TokenTag::Newline,
            Self::parse_struct_field,
        )?;
        Ok(Rc::new(StructDef {
            name,
            ty_args,
            fields,
            id: NodeId::new(),
            attributes,
        }))
    }

    fn parse_struct_field(&mut self) -> Result<Rc<StructField>, Box<Error>> {
        self.skip_newlines();
        let lo = self.index;
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::Colon);
        let ty = self.parse_type()?;
        Ok(Rc::new(StructField {
            name,
            ty,
            loc: self.location(lo),
            id: NodeId::new(),
        }))
    }

    fn parse_enum_def(
        &mut self,
        name: Rc<Identifier>,
        ty_args: Vec<Rc<Polytype>>,
        attributes: Vec<Attribute>,
    ) -> Result<Rc<EnumDef>, Box<Error>> {
        let mut variants: Vec<Rc<Variant>> = vec![];
        loop {
            self.skip_newlines();
            if variants.is_empty() {
                self.expect_token_opt(TokenTag::VBar);
                variants.push(self.parse_variant()?);
            } else if matches!(self.current_token().tag(), TokenTag::VBar) {
                self.consume_token();
                variants.push(self.parse_variant()?);
            } else {
                break;
            }
        }

        Ok(Rc::new(EnumDef {
            name,
            ty_args,
            variants,
            id: NodeId::new(),
            attributes,
        }))
    }

    fn parse_variant(&mut self) -> Result<Rc<Variant>, Box<Error>> {
        self.skip_newlines();
        let lo = self.index;
        let ctor = self.expect_ident()?;
        let mut data = None;
        if self.current_token().tag() == TokenTag::OpenParen {
            data = Some(self.parse_type()?);
        }
        Ok(Rc::new(Variant {
            ctor,
            data,
            loc: self.location(lo),
            id: NodeId::new(),
        }))
    }

    fn parse_output_type_decl(&mut self) -> Result<Rc<InterfaceOutputType>, Box<Error>> {
        self.expect_token(TokenTag::OutputType);
        let name = self.expect_ident()?;
        let mut interfaces = vec![];
        if self.current_token().tag() == TokenTag::Impl {
            self.consume_token();
            while self.current_token().tag() == TokenTag::Ident {
                interfaces.push(self.parse_interface_constraint()?);
            }
        }
        Ok(Rc::new(InterfaceOutputType {
            name,
            interfaces,
            id: NodeId::new(),
        }))
    }

    fn parse_func_decl(&mut self, attributes: Vec<Attribute>) -> Result<Rc<FuncDecl>, Box<Error>> {
        self.skip_newlines();
        self.expect_token(TokenTag::Fn);
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::OpenParen);
        let args =
            self.parse_delimited_list(TokenTag::CloseParen, TokenTag::Comma, Self::parse_func_arg)?;

        self.expect_token(TokenTag::RArrow);

        let ret_type = self.parse_type()?;

        Ok(Rc::new(FuncDecl {
            name,
            args,
            ret_type,
            attributes,
        }))
    }

    fn parse_func_def(&mut self, attributes: Vec<Attribute>) -> Result<Rc<FuncDef>, Box<Error>> {
        self.skip_newlines();
        self.expect_token(TokenTag::Fn);
        let name = self.expect_ident()?;
        self.expect_token(TokenTag::OpenParen);
        let args =
            self.parse_delimited_list(TokenTag::CloseParen, TokenTag::Comma, Self::parse_func_arg)?;
        let mut ret_type = None;
        if self.current_token().tag() == TokenTag::RArrow {
            self.consume_token();
            ret_type = Some(self.parse_type()?);
        }
        if self.current_token().tag() == TokenTag::Eq {
            self.expect_token(TokenTag::Eq);
            let body = self.parse_expr()?;

            Ok(Rc::new(FuncDef {
                name,
                args,
                ret_type,
                body,
                attributes,
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
                attributes,
            }))
        }
    }

    fn parse_func_arg(&mut self) -> Result<ArgMaybeAnnotated, Box<Error>> {
        let name = self.expect_ident()?;
        let mut typ = None;
        if self.current_token().tag() == TokenTag::Colon {
            self.consume_token();
            typ = Some(self.parse_type()?);
        }
        Ok((name, typ))
    }

    // TODO: is this helper necessary now?
    fn parse_statement_block(&mut self) -> Result<Vec<Rc<Stmt>>, Box<Error>> {
        self.expect_token(TokenTag::OpenBrace);
        self.parse_delimited_list(TokenTag::CloseBrace, TokenTag::Newline, Self::parse_stmt)
    }

    fn parse_delimited_list<T>(
        &mut self,
        closing_delimiter: TokenTag,
        separator: TokenTag,
        parse_production: impl Fn(&mut Self) -> Result<T, Box<Error>>,
    ) -> Result<Vec<T>, Box<Error>> {
        let mut productions: Vec<T> = vec![];
        loop {
            self.skip_newlines();
            if self.current_token().tag() == closing_delimiter {
                break;
            }
            productions.push(parse_production(self)?);
            if self.current_token().tag() == separator {
                self.consume_token();
            } else {
                break;
            }
        }
        self.expect_token(closing_delimiter);
        Ok(productions)
    }

    fn parse_expr(&mut self) -> Result<Rc<Expr>, Box<Error>> {
        self.skip_newlines();
        let ret = self.parse_expr_bp(0)?;
        Ok(ret)
    }

    fn parse_expr_bp(&mut self, binding_power: u8) -> Result<Rc<Expr>, Box<Error>> {
        let lo = self.current_token().span.lo;

        // pratt

        // prefix operators
        let mut lhs = if let Some(op) = self.parse_prefix_op() {
            self.consume_token();
            let rhs = self.parse_expr_bp(op.precedence())?;
            Rc::new(Expr {
                kind: ExprKind::Unop(op, rhs).into(),
                loc: self.location(lo),
                id: NodeId::new(),
            })
        } else {
            self.parse_expr_term()?
        };

        loop {
            // postfix operators/expressions
            if let Some(op) = self.parse_postfix_op() {
                if op.precedence() <= binding_power {
                    break;
                }

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
                let args = self.parse_parenthesized_expression_list()?;
                *lhs = Rc::new(Expr {
                    kind: ExprKind::FuncAp(lhs.clone(), args).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                })
            }
            PostfixOp::MemberAccess => {
                self.consume_token();
                let ident = self.expect_ident()?;
                // member access
                // `my_struct.my_field`
                *lhs = Rc::new(Expr {
                    kind: ExprKind::MemberAccess(lhs.clone(), ident).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                })
            }
            PostfixOp::IndexAccess => {
                self.consume_token();
                let index = self.parse_expr()?;
                self.expect_token(TokenTag::CloseBracket);
                *lhs = Rc::new(Expr {
                    kind: ExprKind::IndexAccess(lhs.clone(), index).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                })
            }
            PostfixOp::Unwrap => {
                self.consume_token();
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
        Some(match self.current_token().tag() {
            TokenTag::Plus => BinaryOperator::Add,
            TokenTag::Minus => BinaryOperator::Subtract,
            TokenTag::Star => BinaryOperator::Multiply,
            TokenTag::Slash => BinaryOperator::Divide,
            TokenTag::EqEq => BinaryOperator::Equal,
            TokenTag::NotEq => BinaryOperator::NotEqual,
            TokenTag::Lt => BinaryOperator::LessThan,
            TokenTag::Le => BinaryOperator::LessThanOrEqual,
            TokenTag::Gt => BinaryOperator::GreaterThan,
            TokenTag::Ge => BinaryOperator::GreaterThanOrEqual,
            TokenTag::Mod => BinaryOperator::Mod,
            TokenTag::Caret => BinaryOperator::Pow,
            TokenTag::DotDot => BinaryOperator::Format,
            TokenTag::And => BinaryOperator::And,
            TokenTag::Or => BinaryOperator::Or,
            _ => return None,
        })
    }

    fn parse_assign_op(&mut self) -> Option<AssignOperator> {
        Some(match self.current_token().tag() {
            TokenTag::Eq => AssignOperator::Equal,
            TokenTag::PlusEq => AssignOperator::PlusEq,
            _ => return None,
        })
    }

    fn parse_prefix_op(&mut self) -> Option<PrefixOp> {
        Some(match self.current_token().tag() {
            TokenTag::Minus => {
                let next_tag = self.peek_token(1).tag();
                if next_tag != TokenTag::IntLit && next_tag != TokenTag::FloatLit {
                    PrefixOp::Minus
                } else {
                    return None;
                }
            }
            TokenTag::Not => PrefixOp::Not,
            _ => return None,
        })
    }

    fn parse_postfix_op(&mut self) -> Option<PostfixOp> {
        Some(match self.current_token().tag() {
            TokenTag::OpenParen => PostfixOp::FuncCall,
            TokenTag::Dot => PostfixOp::MemberAccess,
            TokenTag::OpenBracket => PostfixOp::IndexAccess,
            TokenTag::Bang => PostfixOp::Unwrap,
            _ => return None,
        })
    }

    fn try_parse_lambda_expr(&mut self) -> Result<Option<Rc<Expr>>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;

        let mut args: Vec<ArgMaybeAnnotated> = vec![];
        if current.kind == TokenKind::OpenParen {
            self.expect_token(TokenTag::OpenParen);
            match self.parse_delimited_list(
                TokenTag::CloseParen,
                TokenTag::Comma,
                Self::parse_func_arg,
            ) {
                Ok(parsed_args) => args.extend(parsed_args),
                Err(_) => return Ok(None),
            }
        } else if let Ok(arg) = self.parse_func_arg() {
            args.push(arg);
        } else {
            return Ok(None);
        }

        if self.current_token().tag() == TokenTag::RArrow {
            // It must be a lambda
            self.consume_token();
            let body = self.parse_expr()?;
            Ok(Some(
                Expr {
                    kind: Rc::new(ExprKind::AnonymousFunction(args, None, body)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
                .into(),
            ))
        } else {
            Ok(None)
        }
    }

    fn parse_expr_term(&mut self) -> Result<Rc<Expr>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;

        // TODO: this is not the hot path, move it to the _ -> below
        // Try to speculatively parse a lambda expression first
        let checkpoint = self.index;
        let mut checkpoint_errors = mem::take(&mut self.errors);

        if let Some(lambda_expr) = self.try_parse_lambda_expr()? {
            // restore
            checkpoint_errors.extend(self.errors.drain(0..self.errors.len()));
            self.errors = checkpoint_errors;
            return Ok(lambda_expr);
        }

        // rollback
        self.index = checkpoint;
        self.errors = checkpoint_errors;

        // It's not a lambda.
        Ok(Rc::new(match current.kind {
            TokenKind::Ident(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Variable(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Nil => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Nil),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::IntLit(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Int(s.parse::<i64>().unwrap())), // TODO: don't unwrap. report error if this can't fit in an i64
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::FloatLit(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Float(s)), // TODO: make sure float fits in an f64?
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Minus => {
                self.consume_token();
                match self.current_token().kind {
                    TokenKind::IntLit(s) => {
                        self.consume_token();
                        Expr {
                            kind: Rc::new(ExprKind::Int(
                                ("-".to_string() + &s).parse::<i64>().unwrap(),
                            )), // TODO: don't unwrap. report error if this can't fit in an i64
                            loc: self.location(lo),
                            id: NodeId::new(),
                        }
                    }
                    TokenKind::FloatLit(s) => {
                        self.consume_token();
                        Expr {
                            kind: Rc::new(ExprKind::Float("-".to_string() + &s)), // TODO: make sure float fits in an f64?
                            loc: self.location(lo),
                            id: NodeId::new(),
                        }
                    }
                    _ => {
                        return Err(Error::UnexpectedToken(
                            TokenTag::IntLit.to_string(),
                            self.current_token().tag().to_string(),
                            self.current_token_location(),
                        )
                        .into());
                    }
                }
            }
            TokenKind::StringLit(s) => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Str(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::True => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Bool(true)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::False => {
                self.consume_token();
                Expr {
                    kind: Rc::new(ExprKind::Bool(false)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Match => {
                self.expect_token(TokenTag::Match);
                let scrutiny = self.parse_expr()?;
                self.expect_token(TokenTag::OpenBrace);
                let arms = self.parse_delimited_list(
                    TokenTag::CloseBrace,
                    TokenTag::Newline,
                    Self::parse_match_arm,
                )?;
                Expr {
                    kind: Rc::new(ExprKind::Match(scrutiny, arms)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::If => {
                self.expect_token(TokenTag::If);
                let condition = self.parse_expr()?;
                let then_stmt = self.parse_stmt()?;

                let else_stmt = if self.current_token().tag() == TokenTag::Else {
                    self.consume_token();
                    Some(self.parse_stmt()?)
                } else {
                    None
                };

                Expr {
                    kind: Rc::new(ExprKind::IfElse(condition, then_stmt, else_stmt)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::OpenBracket => {
                self.expect_token(TokenTag::OpenBracket);
                let args = self.parse_delimited_list(
                    TokenTag::CloseBracket,
                    TokenTag::Comma,
                    Self::parse_expr,
                )?;
                Expr {
                    kind: Rc::new(ExprKind::Array(args)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::OpenParen => {
                self.consume_token();
                let elems = self.parse_delimited_list(
                    TokenTag::CloseParen,
                    TokenTag::Comma,
                    Self::parse_expr,
                )?;
                if elems.is_empty() {
                    return Err(Error::EmptyParentheses(self.location(lo)).into());
                } else if elems.len() == 1 {
                    //  parenthesized expression
                    return Ok(elems[0].clone());
                } else {
                    Expr {
                        kind: Rc::new(ExprKind::Tuple(elems)),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            TokenKind::Dot => {
                self.consume_token();
                let ident = self.expect_ident()?;
                // member access
                // `.my_enum_variant`
                Expr {
                    kind: ExprKind::MemberAccessLeadingDot(ident).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::OpenBrace => {
                let statements = self.parse_statement_block()?;
                Expr {
                    kind: ExprKind::Block(statements).into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    "expression".into(),
                    current.kind.discriminant().to_string(),
                    self.current_token_location(),
                )
                .into());
            }
        }))
    }

    fn parse_parenthesized_expression_list(&mut self) -> Result<Vec<Rc<Expr>>, Box<Error>> {
        self.expect_token(TokenTag::OpenParen);
        self.parse_delimited_list(TokenTag::CloseParen, TokenTag::Comma, Self::parse_expr)
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
        self.parse_match_pattern_with_prefixes(vec![])
    }

    fn parse_match_pattern_with_prefixes(
        &mut self,
        mut prefixes: Vec<Rc<Identifier>>,
    ) -> Result<Rc<Pat>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Ident(s) => {
                if self.peek_token(1).kind == TokenKind::Dot {
                    prefixes.push(self.expect_ident()?);
                    return self.parse_match_pattern_with_prefixes(prefixes);
                }
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Binding(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Wildcard => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Wildcard),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Nil => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Void),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::True => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Bool(true)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::False => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Bool(false)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::IntLit(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Int(s.parse::<i64>().unwrap())), // TODO: don't unwrap. report error if this can't fit in an i64
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::FloatLit(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Float(s)), // TODO: report error if doesn't fit in f64?
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::StringLit(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Str(s)), // TODO: don't unwrap. report error if this can't fit in an i64
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::OpenParen => {
                self.consume_token();
                let elems = self.parse_delimited_list(
                    TokenTag::CloseParen,
                    TokenTag::Comma,
                    Self::parse_match_pattern,
                )?;
                if elems.is_empty() {
                    return Err(Error::EmptyParentheses(self.location(lo)).into());
                } else if elems.len() == 1 {
                    //  parenthesized pattern
                    return Ok(elems[0].clone());
                } else {
                    Pat {
                        kind: Rc::new(PatKind::Tuple(elems)),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            TokenKind::Dot => {
                self.consume_token();
                let ident = self.expect_ident()?;
                if self.current_token().tag() == TokenTag::OpenParen {
                    // member func call
                    // `.my_enum_variant(`
                    let data = self.parse_match_pattern()?;
                    Pat {
                        kind: PatKind::Variant(prefixes, ident, Some(data)).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                } else {
                    // member access
                    // `.my_enum_variant`
                    let data = None;
                    Pat {
                        kind: PatKind::Variant(prefixes, ident, data).into(),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    "match arm pattern".into(),
                    current.kind.discriminant().to_string(),
                    self.current_token_location(),
                )
                .into());
            }
        }))
    }

    fn parse_let_pattern(&mut self) -> Result<Rc<Pat>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        Ok(Rc::new(match current.kind {
            TokenKind::Wildcard => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Wildcard),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Ident(s) => {
                self.consume_token();
                Pat {
                    kind: Rc::new(PatKind::Binding(s)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            // TODO: code duplication with parse_match_pattern(). Make a helper function used by both
            TokenKind::OpenParen => {
                self.consume_token();
                let elems = self.parse_delimited_list(
                    TokenTag::CloseParen,
                    TokenTag::Comma,
                    Self::parse_match_pattern,
                )?;
                if elems.is_empty() {
                    return Err(Error::EmptyParentheses(self.location(lo)).into());
                } else if elems.len() == 1 {
                    //  parenthesized pattern
                    return Ok(elems[0].clone());
                } else {
                    Pat {
                        kind: Rc::new(PatKind::Tuple(elems)),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    "let pattern".into(),
                    current.kind.discriminant().to_string(),
                    self.current_token_location(),
                )
                .into());
            }
        }))
    }

    fn parse_let_pattern_annotated(&mut self) -> Result<PatAnnotated, Box<Error>> {
        let pat = self.parse_let_pattern()?;
        if self.current_token().tag() == TokenTag::Colon {
            self.consume_token();
            let annot = self.parse_type()?;
            Ok((pat, Some(annot)))
        } else {
            Ok((pat, None))
        }
    }

    fn parse_type(&mut self) -> Result<Rc<Type>, Box<Error>> {
        let current = self.current_token();
        let lo = self.current_token().span.lo;
        let typ = Rc::new(match current.kind {
            TokenKind::Int => {
                self.consume_token();
                Type {
                    kind: Rc::new(TypeKind::Int),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Float => {
                self.consume_token();
                Type {
                    kind: Rc::new(TypeKind::Float),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::String => {
                self.consume_token();
                Type {
                    kind: Rc::new(TypeKind::Str),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Bool => {
                self.consume_token();
                Type {
                    kind: Rc::new(TypeKind::Bool),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Void => {
                self.consume_token();
                Type {
                    kind: Rc::new(TypeKind::Void),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Ident(_) => {
                let name = self.expect_ident()?;
                let mut args = vec![];
                if self.current_token().tag() == TokenTag::Lt {
                    self.consume_token();
                    args.extend(self.parse_delimited_list(
                        TokenTag::Gt,
                        TokenTag::Comma,
                        Self::parse_type,
                    )?);
                }
                Type {
                    kind: Rc::new(TypeKind::NamedWithParams(name, args)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Wildcard => {
                self.consume_token();
                Type {
                    kind: Rc::new(TypeKind::Wildcard),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::PolyIdent(_) => {
                let name = self.expect_poly_ident()?;
                let mut interfaces = vec![];
                while self.current_token().tag() == TokenTag::Ident {
                    interfaces.push(self.parse_interface_constraint()?);
                }
                let polytype = Rc::new(Polytype { name, interfaces });
                Type {
                    kind: Rc::new(TypeKind::Poly(polytype)),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::OpenParen => {
                self.consume_token();
                let elems = self.parse_delimited_list(
                    TokenTag::CloseParen,
                    TokenTag::Comma,
                    Self::parse_type,
                )?;
                if elems.is_empty() {
                    return Err(Error::EmptyParentheses(self.location(lo)).into());
                } else if elems.len() == 1 {
                    //  parenthesized expression
                    return Ok(elems[0].clone());
                } else {
                    Type {
                        kind: Rc::new(TypeKind::Tuple(elems)),
                        loc: self.location(lo),
                        id: NodeId::new(),
                    }
                }
            }
            _ => {
                return Err(Error::UnexpectedToken(
                    "type".into(),
                    current.kind.discriminant().to_string(),
                    self.current_token_location(),
                )
                .into());
            }
        });
        if self.current_token().tag() == TokenTag::RArrow {
            // Function type
            // use recursion for right-associativity
            self.consume_token();
            let rhs = self.parse_type()?;
            let mut args: Vec<Rc<Type>> = vec![];
            match &*typ.kind {
                TypeKind::Tuple(tys) => {
                    args.extend(tys.iter().cloned());
                }
                _ => {
                    args.push(typ);
                }
            }
            Ok(Type {
                kind: Rc::new(TypeKind::Function(args, rhs)),
                loc: self.location(lo),
                id: NodeId::new(),
            }
            .into())
        } else {
            Ok(typ)
        }
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
            }
            TokenKind::Break => {
                self.consume_token();
                Stmt {
                    kind: StmtKind::Break.into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
            TokenKind::Continue => {
                self.consume_token();
                Stmt {
                    kind: StmtKind::Continue.into(),
                    loc: self.location(lo),
                    id: NodeId::new(),
                }
            }
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
            _ => {
                let expr = self.parse_expr()?;
                if matches!(
                    &*expr.kind,
                    ExprKind::Variable(_) | ExprKind::IndexAccess(..) | ExprKind::MemberAccess(..)
                ) && let Some(assign_op) = self.parse_assign_op()
                {
                    self.consume_token();
                    let rhs = self.parse_expr()?;
                    Stmt {
                        kind: StmtKind::Assign(expr, assign_op, rhs).into(),
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

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum PrefixOp {
    Not,
    Minus,
}

enum PostfixOp {
    MemberAccess,
    IndexAccess,
    FuncCall,
    Unwrap,
}

impl BinaryOperator {
    pub(crate) fn precedence(&self) -> u8 {
        match self {
            BinaryOperator::Equal | BinaryOperator::NotEqual => 1,
            BinaryOperator::Format => 2,
            BinaryOperator::And | BinaryOperator::Or => 4,
            BinaryOperator::LessThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThan
            | BinaryOperator::GreaterThanOrEqual => 5,
            BinaryOperator::Add | BinaryOperator::Subtract => 6,
            BinaryOperator::Multiply | BinaryOperator::Divide => 7,
            BinaryOperator::Mod => 8,
            BinaryOperator::Pow => 9,
        }
    }
}

impl PrefixOp {
    fn precedence(&self) -> u8 {
        match self {
            PrefixOp::Minus => 6, // same as plus and minus
            PrefixOp::Not => 10,
        }
    }
}

impl PostfixOp {
    fn precedence(&self) -> u8 {
        match self {
            // TODO: should these all just have the same precedence?
            PostfixOp::MemberAccess => 11,
            PostfixOp::IndexAccess => 12,
            PostfixOp::FuncCall => 13,
            PostfixOp::Unwrap => 14,
        }
    }
}
