/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::FileId;
use crate::statics::{Error, StaticsContext};
use std::fmt;
use std::fmt::Formatter;
use strum_macros::EnumDiscriminants;

#[derive(Clone)]
pub(crate) struct Token {
    pub(crate) kind: TokenKind,
    pub(crate) span: Span,
}

#[derive(Clone, PartialEq, EnumDiscriminants)]
#[strum_discriminants(name(TokenTag))]
pub(crate) enum TokenKind {
    /// `=`
    Eq,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `==`
    EqEq,
    /// `!=`
    Ne,
    /// `>=`
    Ge,
    /// `>`
    Gt,
    /// `!`
    Bang,
    // `+`
    Plus,
    // `-`
    Minus,
    // `*`
    Star,
    // `/`
    Slash,
    // `^`
    Caret,
    // `mod`
    Mod,
    // `and`
    And,
    // `or`
    Or,

    /// `.`
    Dot,
    /// `..`
    DotDot,
    /// `,`
    Comma,
    /// `;`
    Semi,
    /// `:`
    Colon,
    /// `->`
    RArrow,
    // `|`
    VBar,
    /// `#`
    Pound,
    /// `(`
    OpenParen,
    /// `)`
    CloseParen,
    /// `{`
    OpenBrace,
    /// `}`
    CloseBrace,
    /// `[`
    OpenBracket,
    /// `]`
    CloseBracket,

    /* Keywords */
    Let,
    Var,
    Type,
    Implement,
    Extend,
    Use,
    Fn,
    Match,
    Break,
    Continue,
    Return,
    While,
    For,
    In,
    If,
    Else,
    True,
    False,

    Int(String), // TODO: intern the strings and just store Ids here later
    Float(String),
    String(String),
    Ident(String),
    Wildcard,

    Newline,
    Eof,
}

impl TokenKind {
    fn nchars(&self) -> usize {
        match self {
            TokenKind::Eq
            | TokenKind::Lt
            | TokenKind::Gt
            | TokenKind::Bang
            | TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Caret
            | TokenKind::Dot
            | TokenKind::Comma
            | TokenKind::Semi
            | TokenKind::Colon
            | TokenKind::Pound
            | TokenKind::OpenParen
            | TokenKind::CloseParen
            | TokenKind::OpenBrace
            | TokenKind::CloseBrace
            | TokenKind::OpenBracket
            | TokenKind::CloseBracket
            | TokenKind::Wildcard
            | TokenKind::Newline
            | TokenKind::VBar
            | TokenKind::Eof => 1,

            TokenKind::Le
            | TokenKind::EqEq
            | TokenKind::Ne
            | TokenKind::Ge
            | TokenKind::DotDot
            | TokenKind::RArrow
            | TokenKind::Fn
            | TokenKind::Or
            | TokenKind::If
            | TokenKind::In => 2,

            TokenKind::Let
            | TokenKind::Var
            | TokenKind::Use
            | TokenKind::For
            | TokenKind::Mod
            | TokenKind::And => 3,

            TokenKind::Type | TokenKind::Else | TokenKind::True => 4,
            TokenKind::Match | TokenKind::Break | TokenKind::While | TokenKind::False => 5,
            TokenKind::Extend | TokenKind::Return => 6,
            TokenKind::Continue => 8,
            TokenKind::Implement => 9,
            TokenKind::Int(s) | TokenKind::Float(s) | TokenKind::Ident(s) => s.chars().count(),
            TokenKind::String(s) => s.chars().count() + 2, // include quotes
        }
    }

    fn keyword_from_str(s: &str) -> Option<Self> {
        Some(match s {
            "let" => TokenKind::Let,
            "var" => TokenKind::Var,
            "type" => TokenKind::Type,
            "implement" => TokenKind::Implement,
            "extend" => TokenKind::Extend,
            "use" => TokenKind::Use,
            "fn" => TokenKind::Fn,
            "match" => TokenKind::Match,
            "mod" => TokenKind::Mod,
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "return" => TokenKind::Return,
            "while" => TokenKind::While,
            "for" => TokenKind::For,
            "in" => TokenKind::In,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            _ => return None,
        })
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct Span {
    pub(crate) lo: usize,
    pub(crate) hi: usize,
}

struct Lexer {
    chars: Vec<char>,
    index: usize,

    tokens: Vec<Token>,
}

impl Lexer {
    fn new(source: &str) -> Self {
        Lexer {
            chars: source.chars().collect(),
            index: 0,
            tokens: vec![],
        }
    }

    fn done(&self) -> bool {
        self.index >= self.chars.len()
    }

    fn current_char(&self) -> char {
        self.chars[self.index]
    }

    fn peek_char(&self, dist: usize) -> Option<&char> {
        self.chars.get(self.index + dist)
    }

    fn emit(&mut self, kind: TokenKind) {
        let len = kind.nchars();
        let span = Span {
            lo: self.index,
            hi: self.index + len - 1,
        };
        self.tokens.push(Token { kind, span });
        self.index += len;
    }

    fn into_tokens(self) -> Vec<Token> {
        self.tokens
    }
}

// TODO: just stick file_id in the file_data as well, annoying to pass both around
pub(crate) fn tokenize_file(ctx: &mut StaticsContext, file_id: FileId) -> Vec<Token> {
    let file_data = ctx.file_db.get(file_id).unwrap();
    let mut lexer = Lexer::new(&file_data.source);
    while !lexer.done() {
        if start_of_ident(lexer.current_char()) {
            let mut ident = String::from(lexer.current_char());

            let mut next = 1;
            while let Some(c) = lexer.peek_char(next)
                && middle_of_ident(*c)
            {
                ident.push(*c);
                next += 1;
            }

            if let Some(kw) = TokenKind::keyword_from_str(&ident) {
                lexer.emit(kw);
            } else {
                lexer.emit(TokenKind::Ident(ident));
            }
            continue;
        }
        if start_of_number(lexer.current_char()) {
            let mut num = String::new();

            let mut next = 0;
            // negative sign
            if lexer.current_char() == '-' {
                num.push('-');
                next += 1;
            }
            // first run of digits
            while let Some(c) = lexer.peek_char(next)
                && c.is_ascii_digit()
            {
                num.push(*c);
                next += 1;
            }
            // potential decimal point
            if let Some('.') = lexer.peek_char(next) {
                num.push('.');
                next += 1;
            } else {
                // no decimal point. it's an integer
                lexer.emit(TokenKind::Int(num));
                continue;
            }
            // more digits after decimal point
            while let Some(c) = lexer.peek_char(next)
                && c.is_ascii_digit()
            {
                num.push(*c);
                next += 1;
            }
            lexer.emit(TokenKind::Float(num));

            continue;
        }
        match lexer.current_char() {
            '(' => lexer.emit(TokenKind::OpenParen),
            ')' => lexer.emit(TokenKind::CloseParen),
            '{' => lexer.emit(TokenKind::OpenBrace),
            '}' => lexer.emit(TokenKind::CloseBrace),
            '[' => lexer.emit(TokenKind::OpenBracket),
            ']' => lexer.emit(TokenKind::CloseBracket),
            ':' => lexer.emit(TokenKind::Colon),
            ';' => lexer.emit(TokenKind::Semi),
            ',' => lexer.emit(TokenKind::Comma),
            '\n' => lexer.emit(TokenKind::Newline),
            '+' => lexer.emit(TokenKind::Plus),
            '*' => lexer.emit(TokenKind::Star),
            '^' => lexer.emit(TokenKind::Caret),
            '#' => lexer.emit(TokenKind::Pound),
            '|' => lexer.emit(TokenKind::VBar),
            '_' => lexer.emit(TokenKind::Wildcard),
            '=' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::EqEq)
                } else {
                    lexer.emit(TokenKind::Eq)
                }
            }
            '<' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::Le)
                } else {
                    lexer.emit(TokenKind::Lt);
                }
            }
            '>' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::Ge)
                } else {
                    lexer.emit(TokenKind::Gt);
                }
            }
            '!' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::Ne);
                } else {
                    lexer.emit(TokenKind::Bang);
                }
            }
            '-' => {
                if let Some('>') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::RArrow);
                } else {
                    lexer.emit(TokenKind::Minus);
                }
            }
            '.' => {
                if let Some('.') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::DotDot);
                } else {
                    lexer.emit(TokenKind::Dot);
                }
            }
            '"' => {
                let mut s = String::new();

                let mut next = 1;
                // first run of digits
                while let Some(c) = lexer.peek_char(next)
                    && *c != '"'
                {
                    s.push(*c);
                    next += 1;
                }

                lexer.emit(TokenKind::String(s))
            }
            '/' => {
                if let Some('/') = lexer.peek_char(1) {
                    // comment
                    let mut next = 1;
                    while let Some(c) = lexer.peek_char(next)
                        && *c != '\n'
                    {
                        next += 1;
                    }
                    lexer.index += next + 1;
                } else {
                    lexer.emit(TokenKind::Slash);
                }
            }
            ' ' | '\t' => {
                // skip space
                lexer.index += 1;
            }
            _ => {
                ctx.errors
                    .push(Error::UnrecognizedToken(file_id, lexer.index));
                lexer.index += 1;
            }
        }
    }

    lexer.emit(TokenKind::Eof);

    lexer.into_tokens()
}

fn start_of_ident(c: char) -> bool {
    matches!(c, '_' | 'a'..='z' | 'A'..='Z')
}

fn middle_of_ident(c: char) -> bool {
    matches!(c, '_' | '0'..='9' | 'a'..='z' | 'A'..='Z')
}

fn start_of_number(c: char) -> bool {
    c.is_ascii_digit()
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TokenKind::Eq => write!(f, "="),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Le => write!(f, "<="),
            TokenKind::EqEq => write!(f, "=="),
            TokenKind::Ne => write!(f, "!="),
            TokenKind::Ge => write!(f, ">="),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::Mod => write!(f, "mod"),
            TokenKind::And => write!(f, "and"),
            TokenKind::Or => write!(f, "or"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::DotDot => write!(f, ".."),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semi => write!(f, ";"),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::RArrow => write!(f, "->"),
            TokenKind::VBar => write!(f, "|"),
            TokenKind::Pound => write!(f, "#"),
            TokenKind::OpenParen => write!(f, "("),
            TokenKind::CloseParen => write!(f, ")"),
            TokenKind::OpenBrace => write!(f, "{{"),
            TokenKind::CloseBrace => write!(f, "}}"),
            TokenKind::OpenBracket => write!(f, "["),
            TokenKind::CloseBracket => write!(f, "]"),
            TokenKind::Wildcard => write!(f, "_"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::Var => write!(f, "var"),
            TokenKind::Type => write!(f, "type"),
            TokenKind::Implement => write!(f, "implement"),
            TokenKind::Extend => write!(f, "extend"),
            TokenKind::Use => write!(f, "use"),
            TokenKind::Fn => write!(f, "fn"),
            TokenKind::Match => write!(f, "match"),
            TokenKind::Break => write!(f, "break"),
            TokenKind::Continue => write!(f, "continue"),
            TokenKind::Return => write!(f, "return"),
            TokenKind::While => write!(f, "while"),
            TokenKind::For => write!(f, "for"),
            TokenKind::In => write!(f, "in"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::True => write!(f, "true"),
            TokenKind::False => write!(f, "false"),
            TokenKind::Int(s) => write!(f, "{}", s),
            TokenKind::Float(s) => write!(f, "{}", s),
            TokenKind::String(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            TokenKind::Newline => writeln!(f),
            TokenKind::Eof => write!(f, "<EOF>"),
        }
    }
}
impl fmt::Display for TokenTag {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self {
            TokenTag::Eq => write!(f, "="),
            TokenTag::Lt => write!(f, "<"),
            TokenTag::Le => write!(f, "<="),
            TokenTag::EqEq => write!(f, "=="),
            TokenTag::Ne => write!(f, "!="),
            TokenTag::Ge => write!(f, ">="),
            TokenTag::Gt => write!(f, ">"),
            TokenTag::Bang => write!(f, "!"),
            TokenTag::Plus => write!(f, "+"),
            TokenTag::Minus => write!(f, "-"),
            TokenTag::Star => write!(f, "*"),
            TokenTag::Slash => write!(f, "/"),
            TokenTag::Caret => write!(f, "^"),
            TokenTag::Mod => write!(f, "mod"),
            TokenTag::And => write!(f, "and"),
            TokenTag::Or => write!(f, "or"),
            TokenTag::Dot => write!(f, "."),
            TokenTag::DotDot => write!(f, ".."),
            TokenTag::Comma => write!(f, ","),
            TokenTag::Semi => write!(f, ";"),
            TokenTag::Colon => write!(f, ":"),
            TokenTag::RArrow => write!(f, "->"),
            TokenTag::VBar => write!(f, "|"),
            TokenTag::Pound => write!(f, "#"),
            TokenTag::OpenParen => write!(f, "("),
            TokenTag::CloseParen => write!(f, ")"),
            TokenTag::OpenBrace => write!(f, "{{"),
            TokenTag::CloseBrace => write!(f, "}}"),
            TokenTag::OpenBracket => write!(f, "["),
            TokenTag::CloseBracket => write!(f, "]"),
            TokenTag::Wildcard => write!(f, "_"),
            TokenTag::Let => write!(f, "let"),
            TokenTag::Var => write!(f, "var"),
            TokenTag::Type => write!(f, "type"),
            TokenTag::Implement => write!(f, "implement"),
            TokenTag::Extend => write!(f, "extend"),
            TokenTag::Use => write!(f, "use"),
            TokenTag::Fn => write!(f, "fn"),
            TokenTag::Match => write!(f, "match"),
            TokenTag::Break => write!(f, "break"),
            TokenTag::Continue => write!(f, "continue"),
            TokenTag::Return => write!(f, "return"),
            TokenTag::While => write!(f, "while"),
            TokenTag::For => write!(f, "for"),
            TokenTag::In => write!(f, "in"),
            TokenTag::If => write!(f, "if"),
            TokenTag::Else => write!(f, "else"),
            TokenTag::True => write!(f, "true"),
            TokenTag::False => write!(f, "false"),
            TokenTag::Int => write!(f, "int literal"),
            TokenTag::Float => write!(f, "float literal"),
            TokenTag::String => write!(f, "string literal"),
            TokenTag::Ident => write!(f, "identifier"),
            TokenTag::Newline => write!(f, "newline"),
            TokenTag::Eof => write!(f, "<EOF>"),
        }
    }
}
