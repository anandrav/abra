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

    fn slice(&self, begin: usize, end: usize) -> &[char] {
        &self.chars[self.index + begin..self.index + end]
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

    fn at_triple_quote(&self, offset: usize) -> bool {
        self.peek_char(offset) == Some('"')
            && self.peek_char(offset + 1) == Some('"')
            && self.peek_char(offset + 2) == Some('"')
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
                if lexer.at_triple_quote(0) {
                    handle_multiline_string(&mut lexer, ctx, file_id);
                    continue;
                }
                let open = lexer.index;
                let n_off = lexer.chars.len() - open;
                let (content_end, after_close) =
                    match scan_for_unescaped_delim(&lexer, 1, &['"'], false) {
                        Some(c) => (c, c + 1),
                        None => (n_off, n_off),
                    };
                let mut s = String::new();
                process_escapes_into(&mut s, lexer.slice(1, content_end), ctx, file_id);
                emit_string_token(&mut lexer, s, open, open + after_close);
            }
            '\'' => {
                let open = lexer.index;
                let n_off = lexer.chars.len() - open;
                let (content_end, after_close) =
                    match scan_for_unescaped_delim(&lexer, 1, &['\''], false) {
                        Some(c) => (c, c + 1),
                        None => (n_off, n_off),
                    };
                let mut s = String::new();
                process_escapes_into(&mut s, lexer.slice(1, content_end), ctx, file_id);
                emit_string_token(&mut lexer, s, open, open + after_close);
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

// All position arguments to these helpers are offsets relative to `lexer.index`.

// Scan forward from `start` for the next unescaped occurrence of `delim`.
// `\X` is treated as an escape pair and skipped (the X is never the start of a delim).
// Returns Some(pos) if found, None on EOF (or on '\n' if `stop_at_newline`).
fn scan_for_unescaped_delim(
    lexer: &Lexer,
    start: usize,
    delim: &[char],
    stop_at_newline: bool,
) -> Option<usize> {
    let dl = delim.len();
    let mut p = start;
    while let Some(c) = lexer.peek_char(p) {
        if stop_at_newline && c == '\n' {
            return None;
        }
        if c == '\\' {
            p += 2;
            continue;
        }
        if (0..dl).all(|i| lexer.peek_char(p + i) == Some(delim[i])) {
            return Some(p);
        }
        p += 1;
    }
    None
}

// Process escape sequences in offsets [start..end], appending decoded chars to `s`.
fn process_escapes_into(s: &mut String, chars: &[char], ctx: &mut StaticsContext, file_id: FileId) {
    let base = 0;
    let mut p = 0;
    let end = chars.len();
    while p < end
        && let Some(c) = chars.get(p).cloned()
    {
        if c == '\\'
            && p + 1 < end
            && let Some(c2) = chars.get(p + 1).cloned()
        {
            match c2 {
                'n' => s.push('\n'),
                't' => s.push('\t'),
                'r' => s.push('\r'),
                '"' => s.push('"'),
                '\'' => s.push('\''),
                '\\' => s.push('\\'),
                'x' => {
                    if p + 3 < end
                        && let Some(d2) = chars.get(p + 2).cloned()
                        && let Some(d3) = chars.get(p + 3).cloned()
                        && let Ok(byte) = u8::from_str_radix(&format!("{d2}{d3}"), 16)
                    {
                        s.push(byte as char);
                        p += 4;
                        continue;
                    }
                    ctx.errors.push(Error::UnrecognizedEscapeSequence(
                        file_id,
                        Span {
                            lo: base + p,
                            hi: base + p + 1,
                        },
                    ));
                }
                _ => ctx.errors.push(Error::UnrecognizedEscapeSequence(
                    file_id,
                    Span {
                        lo: base + p,
                        hi: base + p + 1,
                    },
                )),
            }
            p += 2;
        } else {
            s.push(c);
            p += 1;
        }
    }
}

enum MultilineStringGetlineResult {
    EndsWithTripleQuote(usize, usize),
    EndsWithNewline(usize, usize),
    Empty(usize, usize),
}

impl MultilineStringGetlineResult {
    fn begin(&self) -> usize {
        match self {
            MultilineStringGetlineResult::EndsWithTripleQuote(begin, _)
            | MultilineStringGetlineResult::EndsWithNewline(begin, _)
            | MultilineStringGetlineResult::Empty(begin, _) => *begin,
        }
    }

    fn end(&self) -> usize {
        match self {
            MultilineStringGetlineResult::EndsWithTripleQuote(_, end)
            | MultilineStringGetlineResult::EndsWithNewline(_, end)
            | MultilineStringGetlineResult::Empty(_, end) => *end,
        }
    }
}

fn handle_multiline_string(lexer: &mut Lexer, ctx: &mut StaticsContext, file_id: FileId) {
    let lo = lexer.index;
    let mut next = 3;

    let mut first_line_has_triple_quote = true;

    fn get_line(lexer: &mut Lexer, next: &mut usize) -> Option<MultilineStringGetlineResult> {
        let begin = *next;
        while !lexer.at_triple_quote(*next)
            && let Some(c) = lexer.peek_char(*next)
            && c != '\n'
        {
            *next += 1;
        }

        if lexer.at_triple_quote(*next) {
            let end = *next;
            *next += 3;
            if lexer.slice(begin, end).iter().all(|c| c.is_whitespace()) {
                return None;
            }
            return Some(MultilineStringGetlineResult::EndsWithTripleQuote(
                begin, end,
            ));
        }
        if lexer.peek_char(*next) == Some('\n') {
            let end = *next;
            *next += 1;
            if lexer.slice(begin, end).iter().all(|c| c.is_whitespace()) {
                return Some(MultilineStringGetlineResult::Empty(begin, end));
            }
            return Some(MultilineStringGetlineResult::EndsWithNewline(begin, end));
        }
        None
    }

    let mut lines = vec![];
    loop {
        let line = get_line(lexer, &mut next);
        match line {
            None => {
                break;
            }
            Some(line) => match line {
                MultilineStringGetlineResult::Empty(begin, end) => {
                    if lines.is_empty() {
                        first_line_has_triple_quote = false;
                    } else {
                        lines.push(MultilineStringGetlineResult::Empty(begin, end));
                    }
                }
                MultilineStringGetlineResult::EndsWithTripleQuote(begin, end) => {
                    lines.push(MultilineStringGetlineResult::EndsWithTripleQuote(
                        begin, end,
                    ));
                    break;
                }
                MultilineStringGetlineResult::EndsWithNewline(begin, end) => {
                    lines.push(MultilineStringGetlineResult::EndsWithNewline(begin, end));
                }
            },
        }
    }

    fn calculate_indent(lexer: &mut Lexer, mut begin: usize) -> usize {
        let mut indent = 0;
        while matches!(lexer.peek_char(begin), Some(' ' | '\t')) {
            if matches!(lexer.peek_char(begin), Some(' ')) {
                indent += 1
            }
            if matches!(lexer.peek_char(begin), Some('\t')) {
                indent += 4
            }
            begin += 1;
        }
        indent
    }

    let mut indent = usize::MAX;
    for (i, line) in lines.iter().enumerate() {
        if i == 0 && first_line_has_triple_quote {
            continue;
        }
        match line {
            MultilineStringGetlineResult::EndsWithTripleQuote(begin, _)
            | MultilineStringGetlineResult::EndsWithNewline(begin, _) => {
                indent = indent.min(calculate_indent(lexer, *begin))
            }
            MultilineStringGetlineResult::Empty(_, _) => {}
        }
    }
    let mut string_val = "".to_string();
    for (i, line) in lines.iter().enumerate() {
        let begin = line.begin();
        let end = line.end();

        let slice2 = lexer.index + end;
        let modified_indent = if i == 0 && first_line_has_triple_quote {
            0
        } else {
            indent
        };
        let slice1 = slice2.min(lexer.index + begin + modified_indent);

        for c in &lexer.chars[slice1..slice2] {
            string_val.push(*c);
        }

        if i < lines.len() - 1 {
            string_val.push('\n');
        }
    }

    let mut string_val_processed_escapes = "".to_string();
    process_escapes_into(
        &mut string_val_processed_escapes,
        &string_val.chars().collect::<Vec<_>>(),
        ctx,
        file_id,
    );
    emit_string_token(lexer, string_val_processed_escapes, lo, lexer.index + next);
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
