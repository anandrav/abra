/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::FileId;
use crate::statics::{Error, StaticsContext};
use std::fmt;
use std::fmt::Formatter;
use std::str::FromStr;
use strum::IntoDiscriminant;
use strum_macros::{EnumDiscriminants, EnumString, IntoStaticStr};

#[derive(Clone)]
pub(crate) struct Token {
    pub(crate) kind: TokenKind,
    pub(crate) span: Span,
}

impl Token {
    pub(crate) fn tag(&self) -> TokenTag {
        self.kind.discriminant()
    }
}

#[derive(Clone, PartialEq, EnumDiscriminants, EnumString)]
#[strum_discriminants(name(TokenTag))]
#[strum_discriminants(derive(IntoStaticStr))]
#[strum(serialize_all = "lowercase")]
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
    NotEq,
    /// `>=`
    Ge,
    /// `>`
    Gt,
    /// `!`
    Bang,
    /// `?`
    Question,
    // `+`
    Plus,
    // `+=`
    PlusEq,
    // `-`
    Minus,
    // `-=`
    MinusEq,
    // `*`
    Star,
    // '*='
    StarEq,
    // `/`
    Slash,
    // '/='
    SlashEq,
    // `^`
    Caret,
    // `%`
    Mod,
    // '%='
    ModEq,
    // `and`
    And,
    // `or`
    Or,
    // `not`
    Not,

    /// `.`
    Dot,
    /// `..`
    DotDot,
    /// `,`
    Comma,
    /// `:`
    Colon,
    /// ';'
    Semicolon,
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
    Interface,
    #[strum(serialize = "outputtype")]
    OutputType,
    Implement,
    Impl, // TODO: re-evaluate having both of these keywords
    Extend,
    Use,
    As,
    Except,
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
    Nil,
    True,
    False,
    Int,
    Float,
    Bool,
    String,
    Void,

    IntLit(String), // TODO: intern the strings and just store Ids here later
    FloatLit(String),
    StringLit(String),
    Ident(String),
    PolyIdent(String), // T, U, V, T2, T123 etc.
    Wildcard,

    Newline,
    Eof,
}

impl TokenKind {
    fn nchars(&self) -> usize {
        match self {
            TokenKind::Newline | TokenKind::Eof => 1,
            TokenKind::IntLit(s)
            | TokenKind::FloatLit(s)
            | TokenKind::Ident(s)
            | TokenKind::PolyIdent(s) => s.chars().count(),
            TokenKind::StringLit(s) => {
                let mut ret = 0;
                for char in s.chars() {
                    match char {
                        '\n' | '\t' | '\r' | '\\' | '"' => ret += 2,
                        c if (c as u32) < 0x20 || (c as u32) == 0x7f => ret += 4, // \xNN
                        _ => ret += 1,
                    }
                }
                ret + 2
            } // include quotes
            _ => self.discriminant().as_str().chars().count(),
        }
    }

    fn keyword_from_str(s: &str) -> Option<Self> {
        let ret = TokenKind::from_str(s).ok();
        if let Some(kind) = &ret
            && kind.is_keyword()
        {
            return ret;
        }
        None
    }

    pub fn is_keyword(&self) -> bool {
        match self {
            TokenKind::Let
            | TokenKind::Var
            | TokenKind::Type
            | TokenKind::Interface
            | TokenKind::OutputType
            | TokenKind::Implement
            | TokenKind::Impl
            | TokenKind::Extend
            | TokenKind::Use
            | TokenKind::As
            | TokenKind::Except
            | TokenKind::Fn
            | TokenKind::Match
            | TokenKind::And
            | TokenKind::Or
            | TokenKind::Not
            | TokenKind::Break
            | TokenKind::Continue
            | TokenKind::Return
            | TokenKind::While
            | TokenKind::For
            | TokenKind::In
            | TokenKind::If
            | TokenKind::Else
            | TokenKind::Nil
            | TokenKind::True
            | TokenKind::False
            | TokenKind::Int
            | TokenKind::Float
            | TokenKind::Bool
            | TokenKind::String
            | TokenKind::Void => true,

            TokenKind::Eq
            | TokenKind::Lt
            | TokenKind::Le
            | TokenKind::EqEq
            | TokenKind::NotEq
            | TokenKind::Ge
            | TokenKind::Gt
            | TokenKind::Bang
            | TokenKind::Question
            | TokenKind::Plus
            | TokenKind::PlusEq
            | TokenKind::Minus
            | TokenKind::MinusEq
            | TokenKind::Star
            | TokenKind::StarEq
            | TokenKind::Slash
            | TokenKind::SlashEq
            | TokenKind::Caret
            | TokenKind::Mod
            | TokenKind::ModEq
            | TokenKind::Dot
            | TokenKind::DotDot
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Semicolon
            | TokenKind::RArrow
            | TokenKind::VBar
            | TokenKind::Pound
            | TokenKind::OpenParen
            | TokenKind::CloseParen
            | TokenKind::OpenBrace
            | TokenKind::CloseBrace
            | TokenKind::OpenBracket
            | TokenKind::CloseBracket
            | TokenKind::Wildcard
            | TokenKind::Newline
            | TokenKind::Eof
            | TokenKind::IntLit(_)
            | TokenKind::FloatLit(_)
            | TokenKind::StringLit(_)
            | TokenKind::Ident(_)
            | TokenKind::PolyIdent(_) => false,
        }
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

    fn peek_char(&self, dist: usize) -> Option<char> {
        // TODO: just return EOF instead of None
        self.chars.get(self.index + dist).cloned()
    }

    fn emit(&mut self, kind: TokenKind) {
        let len = kind.nchars();
        let span = Span {
            lo: self.index,
            hi: self.index + len,
        };
        self.tokens.push(Token { kind, span });
        self.index += len;
    }

    fn emit_with_skipped(&mut self, kind: TokenKind, skipped_chars: usize) {
        let len = kind.nchars() + skipped_chars;
        let span = Span {
            lo: self.index,
            hi: self.index + len,
        };
        self.tokens.push(Token { kind, span });
        self.index += len;
    }

    fn into_tokens(self) -> Vec<Token> {
        self.tokens
    }

    fn handle_num(&mut self) {
        let mut num = String::new();

        let mut next = 0;
        let mut skipped_chars = 0;
        // negative sign
        if self.current_char() == '-' {
            num.push('-');
            next += 1;
        }
        // first run of digits
        while let Some(c) = self.peek_char(next)
            && (c.is_ascii_digit() || c == '_')
        {
            if c.is_ascii_digit() {
                num.push(c);
            } else {
                skipped_chars += 1;
            }
            next += 1;
        }
        // potential decimal point
        if let Some('.') = self.peek_char(next) {
            num.push('.');
            next += 1;
        } else {
            // no decimal point. it's an integer
            self.emit_with_skipped(TokenKind::IntLit(num), skipped_chars);
            return;
        }
        // more digits after decimal point
        while let Some(c) = self.peek_char(next)
            && (c.is_ascii_digit() || c == '_')
        {
            if c.is_ascii_digit() {
                num.push(c);
            } else {
                skipped_chars += 1;
            }
            next += 1;
        }
        self.emit_with_skipped(TokenKind::FloatLit(num), skipped_chars);
    }
}

// TODO: just stick file_id in the file_data as well, annoying to pass both around
pub(crate) fn tokenize_file(ctx: &mut StaticsContext, file_id: FileId) -> Vec<Token> {
    let file_data = ctx.file_db.get(file_id).unwrap();
    let mut lexer = Lexer::new(&file_data.source);

    // look for a shebang at the beginning of file
    if !lexer.done()
        && lexer.current_char() == '#'
        && let Some('!') = lexer.peek_char(1)
    {
        // skip the rest of the line
        let mut next = 1;
        while let Some(c) = lexer.peek_char(next)
            && c != '\n'
        {
            next += 1;
        }
        lexer.index += next;
    }
    while !lexer.done() {
        if start_of_ident(lexer.current_char()) {
            let mut ident = String::from(lexer.current_char());

            let mut next = 1;
            while let Some(c) = lexer.peek_char(next)
                && middle_of_ident(c)
            {
                ident.push(c);
                next += 1;
            }

            // since identifiers can start with '_', must handle wildcard here
            if ident == "_" {
                lexer.emit(TokenKind::Wildcard);
                continue;
            }

            if let Some(kw) = TokenKind::keyword_from_str(&ident) {
                lexer.emit(kw);
            } else if is_poly_ident(&ident) {
                lexer.emit(TokenKind::PolyIdent(ident));
            } else {
                lexer.emit(TokenKind::Ident(ident));
            }
            continue;
        }
        if start_of_number(lexer.current_char()) {
            lexer.handle_num();

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
            ';' => lexer.emit(TokenKind::Semicolon),
            ',' => lexer.emit(TokenKind::Comma),
            '\n' => lexer.emit(TokenKind::Newline),
            '?' => lexer.emit(TokenKind::Question),
            '*' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::StarEq)
                } else {
                    lexer.emit(TokenKind::Star)
                }
            }
            '%' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::ModEq)
                } else {
                    lexer.emit(TokenKind::Mod)
                }
            }
            '^' => lexer.emit(TokenKind::Caret),
            '#' => lexer.emit(TokenKind::Pound),
            '|' => lexer.emit(TokenKind::VBar),
            '+' => {
                if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::PlusEq)
                } else {
                    lexer.emit(TokenKind::Plus)
                }
            }
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
                    lexer.emit(TokenKind::NotEq);
                } else {
                    lexer.emit(TokenKind::Bang);
                }
            }
            '-' => {
                if let Some('>') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::RArrow);
                } else if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::MinusEq)
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
                if lexer.peek_char(1) == Some('"') && lexer.peek_char(2) == Some('"') {
                    handle_multiline_string(&mut lexer, ctx, file_id);
                    continue;
                }
                let open = lexer.index;
                let after_open = open + 1;
                let n = lexer.chars.len();
                let close =
                    scan_for_unescaped_delim(&lexer.chars, after_open, &['"'], false).unwrap_or(n);
                let after_close = (close + 1).min(n);
                let mut s = String::new();
                process_escapes_into(&mut s, &lexer.chars, after_open, close, ctx, file_id);
                lexer.tokens.push(Token {
                    kind: TokenKind::StringLit(s),
                    span: Span {
                        lo: open,
                        hi: after_close,
                    },
                });
                lexer.index = after_close;
            }
            '/' => {
                if let Some('/') = lexer.peek_char(1) {
                    // single-line comment
                    let mut next = 1;
                    while let Some(c) = lexer.peek_char(next)
                        && c != '\n'
                    {
                        next += 1;
                    }
                    lexer.index += next;
                } else if let Some('*') = lexer.peek_char(1) {
                    // multi-line comment
                    let mut next = 2;
                    while let Some(c) = lexer.peek_char(next)
                        && let Some(c2) = lexer.peek_char(next + 1)
                        && c != '*'
                        && c2 != '/'
                    {
                        next += 1;
                    }
                    lexer.index += next + 2;
                } else if let Some('=') = lexer.peek_char(1) {
                    lexer.emit(TokenKind::SlashEq)
                } else {
                    lexer.emit(TokenKind::Slash);
                }
            }
            ' ' | '\t' => {
                // skip space
                lexer.index += 1;
            }
            '\\' if Some('\n') == lexer.peek_char(1) => {
                // line continuation
                lexer.index += 2;
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

// Scan forward from `start` for the next unescaped occurrence of `delim`.
// `\X` is treated as an escape pair and skipped (the X is never the start of a delim).
// Returns Some(pos) if found, None on EOF (or on '\n' if `stop_at_newline`).
fn scan_for_unescaped_delim(
    chars: &[char],
    start: usize,
    delim: &[char],
    stop_at_newline: bool,
) -> Option<usize> {
    let n = chars.len();
    let dl = delim.len();
    let mut p = start;
    while p < n {
        let c = chars[p];
        if stop_at_newline && c == '\n' {
            return None;
        }
        if c == '\\' {
            p = (p + 2).min(n);
            continue;
        }
        if p + dl <= n && (0..dl).all(|i| chars[p + i] == delim[i]) {
            return Some(p);
        }
        p += 1;
    }
    None
}

// Process escape sequences in chars[start..end], appending decoded chars to `s`.
// Spans pushed for errors are absolute positions in the source.
fn process_escapes_into(
    s: &mut String,
    chars: &[char],
    start: usize,
    end: usize,
    ctx: &mut StaticsContext,
    file_id: FileId,
) {
    let mut p = start;
    while p < end {
        let c = chars[p];
        if c == '\\' && p + 1 < end {
            match chars[p + 1] {
                'n' => s.push('\n'),
                't' => s.push('\t'),
                'r' => s.push('\r'),
                '"' => s.push('"'),
                '\\' => s.push('\\'),
                'x' => {
                    if p + 3 < end
                        && let Ok(byte) =
                            u8::from_str_radix(&format!("{}{}", chars[p + 2], chars[p + 3]), 16)
                    {
                        s.push(byte as char);
                        p += 4;
                        continue;
                    }
                    ctx.errors.push(Error::UnrecognizedEscapeSequence(
                        file_id,
                        Span { lo: p, hi: p + 1 },
                    ));
                }
                _ => ctx.errors.push(Error::UnrecognizedEscapeSequence(
                    file_id,
                    Span { lo: p, hi: p + 1 },
                )),
            }
            p += 2;
        } else {
            s.push(c);
            p += 1;
        }
    }
}

// Handle a triple-quoted multiline string starting at `lexer.index` (where
// `chars[index..][..3]` is `"""`). Two cases:
//   B (single-line): closing `"""` appears on the same line as the opener.
//      Content is the chars between, escape-processed, no indent stripping.
//   A (multi-line): closing `"""` appears on a later line preceded only by
//      whitespace. That whitespace is the indent prefix; it is stripped from
//      every non-blank content line. Insufficient indent → error, but the
//      line is still included verbatim. Opener-line residue (chars between
//      `"""` and the first newline) becomes the first content line if non-blank,
//      and is not subject to prefix stripping.
// On EOF before a closer: emit what we have and advance to EOF.
fn handle_multiline_string(lexer: &mut Lexer, ctx: &mut StaticsContext, file_id: FileId) {
    const TQ: [char; 3] = ['"', '"', '"'];
    let open = lexer.index;
    let after_open = open + 3;
    let n = lexer.chars.len();
    let chars = &lexer.chars;
    let is_hws = |c: char| matches!(c, ' ' | '\t');

    // Case B: opener and closer on the same line.
    if let Some(close) = scan_for_unescaped_delim(chars, after_open, &TQ, true) {
        let mut s = String::new();
        process_escapes_into(&mut s, chars, after_open, close, ctx, file_id);
        emit_string_token(lexer, s, open, close + 3);
        return;
    }

    // Case A. Walk to the opener-line newline; the chars before it are the residue.
    let mut p = after_open;
    while p < n && chars[p] != '\n' {
        p += 1;
    }
    let opener_line_end = p;
    let residue_is_blank = (after_open..opener_line_end).all(|i| is_hws(chars[i]));

    // Walk body lines after the opener-line newline until closer or EOF. Each
    // body line is recorded as (line_start, line_end_excluding_newline).
    let mut body_lines: Vec<(usize, usize)> = vec![];
    let mut prefix: std::ops::Range<usize> = 0..0;
    let after_close = if p < n {
        p += 1; // skip opener-line \n
        loop {
            let ws_start = p;
            while p < n && is_hws(chars[p]) {
                p += 1;
            }
            if chars[p..].starts_with(&TQ) {
                prefix = ws_start..p;
                break p + 3;
            }
            while p < n && chars[p] != '\n' {
                p += 1;
            }
            body_lines.push((ws_start, p));
            if p >= n {
                break n;
            }
            p += 1;
        }
    } else {
        n
    };

    // Render: residue (no strip) chained with body lines (with strip).
    let residue = (!residue_is_blank).then_some((after_open, opener_line_end));
    let lines = residue
        .into_iter()
        .map(|r| (r, false))
        .chain(body_lines.iter().copied().map(|l| (l, true)));

    let mut s = String::new();
    let mut emitted = false;
    for ((ls, le), can_strip) in lines {
        if emitted {
            s.push('\n');
        }
        emitted = true;
        if (ls..le).all(|j| is_hws(chars[j])) {
            continue;
        }
        let strip = if can_strip && !prefix.is_empty() {
            let pl = prefix.len();
            let ok = le - ls >= pl && (0..pl).all(|k| chars[ls + k] == chars[prefix.start + k]);
            if !ok {
                ctx.errors.push(Error::InsufficientIndentation(
                    file_id,
                    Span { lo: ls, hi: le },
                ));
                0
            } else {
                pl
            }
        } else {
            0
        };
        process_escapes_into(&mut s, chars, ls + strip, le, ctx, file_id);
    }

    emit_string_token(lexer, s, open, after_close);
}

fn emit_string_token(lexer: &mut Lexer, s: String, lo: usize, hi: usize) {
    lexer.tokens.push(Token {
        kind: TokenKind::StringLit(s),
        span: Span { lo, hi },
    });
    lexer.index = hi;
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
            TokenKind::IntLit(s) => write!(f, "{}", s),
            TokenKind::FloatLit(s) => write!(f, "{}", s),
            TokenKind::StringLit(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            _ => write!(f, "{}", self.kind.discriminant()),
        }
    }
}

fn is_poly_ident(ident: &str) -> bool {
    if ident.is_empty() {
        return false;
    }
    let mut chars = ident.chars();
    if !chars.next().unwrap().is_uppercase() {
        return false;
    }
    for char in chars {
        if char.is_alphabetic() {
            return false;
        }
    }
    true
}

impl TokenTag {
    fn as_str(&self) -> &str {
        match &self {
            TokenTag::Eq => "=",
            TokenTag::Lt => "<",
            TokenTag::Le => "<=",
            TokenTag::EqEq => "==",
            TokenTag::NotEq => "!=",
            TokenTag::Ge => ">=",
            TokenTag::Gt => ">",
            TokenTag::Bang => "!",
            TokenTag::Question => "?",
            TokenTag::Plus => "+",
            TokenTag::PlusEq => "+=",
            TokenTag::Minus => "-",
            TokenTag::MinusEq => "-=",
            TokenTag::Star => "*",
            TokenTag::StarEq => "*=",
            TokenTag::Slash => "/",
            TokenTag::SlashEq => "/=",
            TokenTag::Caret => "^",
            TokenTag::Mod => "%",
            TokenTag::ModEq => "%=",
            TokenTag::Dot => ".",
            TokenTag::DotDot => "..",
            TokenTag::Comma => ",",
            TokenTag::Colon => ":",
            TokenTag::Semicolon => ";",
            TokenTag::RArrow => "->",
            TokenTag::VBar => "|",
            TokenTag::Pound => "#",
            TokenTag::OpenParen => "(",
            TokenTag::CloseParen => ")",
            TokenTag::OpenBrace => "{",
            TokenTag::CloseBrace => "}",
            TokenTag::OpenBracket => "[",
            TokenTag::CloseBracket => "]",
            TokenTag::Wildcard => "_",
            _ => self.into(), // use strum IntoStaticStr
        }
    }
}

impl fmt::Display for TokenTag {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
