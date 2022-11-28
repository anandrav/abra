use operators::BinOpcode;
use std::rc::Rc;
use types::Type;
lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

pub fn parse(source: &str) -> Result<Rc<Expr>, String> {
    abra_grammar::ExprParser::new()
        .parse(source)
        .map_err(|err| err.to_string())
}

// pub fn parse2(token_tree: Rc<TokenTree>) -> Rc<Expr> {
//     let TokenTree::Children { children, kind } = &*token_tree else {
//         panic!("block expression token tree malformed")
//     };
//     match kind {
//         _ => todo!(),
//     }
// }

// pub fn fix(s: &str) -> String {
//     // debug_println!("fix: {}", s);
//     if let Err(e) = MyParser::parse(Rule::program, &s) {
//         if let ErrorVariant::ParsingError {
//             positives,
//             negatives,
//         } = e.variant
//         {
//             if positives.contains(&Rule::placeholder) {
//                 let mut s = String::from(s);
//                 if let Pos(p) = e.location {
//                     s.insert_str(p, &Token::Placeholder.to_str());
//                     return fix(&s);
//                 }
//             }
//         }
//         // debug_println!("{:#?}", e);
//         panic!()
//     }
//     s.to_string()
// }

#[derive(Debug, PartialEq)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub stmtkind: Rc<StmtKind>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum StmtKind {
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>),
    Expr(Rc<Expr>),
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub exprkind: Rc<ExprKind>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    // EmptyHole,
    // InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>, Option<Rc<Expr>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, Vec<Rc<Expr>>),
}

pub type MatchArm = (Rc<Pat>, Rc<Expr>);

#[derive(Debug, PartialEq)]
pub struct Pat {
    pub patkind: Rc<PatKind>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum PatKind {
    // EmptyHole,
    // InvalidText(String),
    Var(Identifier),
    // Unit,
    // Int(i32),
    // Bool(bool),
    // Str(String),
}
