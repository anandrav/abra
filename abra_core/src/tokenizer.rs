use crate::FileData;
use crate::ast::FileId;
use crate::statics::{Error, StaticsContext};
use std::fmt;
use std::fmt::Formatter;

pub(crate) struct Token {
    kind: TokenKind,
    span: Span,
}

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

    Int(String),
    Float(String),
    String(String),
    Ident(String),

    Newline,
    Eof,
}

impl TokenKind {
    fn len(&self) -> usize {
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
            | TokenKind::Newline
            | TokenKind::VBar
            | TokenKind::Eof => 1,

            TokenKind::Le
            | TokenKind::EqEq
            | TokenKind::Ne
            | TokenKind::Ge
            | TokenKind::DotDot
            | TokenKind::RArrow
            | TokenKind::Fn => 2,

            TokenKind::Let | TokenKind::Var | TokenKind::Use => 3,

            TokenKind::Type => 4,
            TokenKind::Extend => 6,
            TokenKind::Implement => 9,
            TokenKind::Int(s) | TokenKind::Float(s) | TokenKind::Ident(s) => s.len(),
            TokenKind::String(s) => s.len() + 2,
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
            _ => return None,
        })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Span {
    lo: usize,
    hi: usize,
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
        let len = kind.len();
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
            c => {
                // TODO: error needs location info. But can't use Node. Must pass span of token and file_id
                ctx.errors
                    .push(Error::UnrecognizedToken(file_id, lexer.index));
                lexer.index += 1;
            }
        }
    }

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
            TokenKind::Let => write!(f, "let"),
            TokenKind::Var => write!(f, "var"),
            TokenKind::Type => write!(f, "type"),
            TokenKind::Implement => write!(f, "implement"),
            TokenKind::Extend => write!(f, "extend"),
            TokenKind::Use => write!(f, "use"),
            TokenKind::Fn => write!(f, "fn"),
            TokenKind::Int(s) => write!(f, "{}", s),
            TokenKind::Float(s) => write!(f, "{}", s),
            TokenKind::String(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            TokenKind::Newline => writeln!(f),
            TokenKind::Eof => write!(f, "<EOF>"),
        }
    }
}
