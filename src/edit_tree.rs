use operators::BinOpcode;
use regex::Regex;
use std::collections::VecDeque;
use std::rc::Rc;
use types::Type;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug)]
pub struct Exp(Operand);

pub type Pat = (); // TODO

pub type Rule = (Pat, Exp);

#[derive(Debug)]
pub enum Operand {
    Hole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),

    Block(VecDeque<OpSeq>),
    // Let(Rc<Pat>, Option<Rc<Type>>, Rc<OpSeq>, Rc<OpSeq>),
    // Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<OpSeq>),
    If(Rc<OpSeq>, Rc<OpSeq>, Rc<OpSeq>),
    Match(Rc<OpSeq>, Vec<Rule>),
}

pub type OpSeq = VecDeque<OpSeqToken>;

#[derive(Debug)]
pub enum OpSeqToken {
    Operand(Operand),
    Operator(Operator),
    Space(Whitespace),
}

#[derive(Debug)]
pub enum Whitespace {
    Space,
    Newline,
}

#[derive(Debug)]
pub enum Operator {
    InvalidText(String),
    Valid(BinOpcode),
}

pub type ZExp = ZOperand;

pub type ZPat = (); // TODO

pub type ZRuleL = (ZPat, Exp);

pub type ZRuleR = (Pat, ZExp);

#[derive(Debug)]
pub enum ZOperand {
    Hole(CursorPosition),
    Block(VecDeque<OpSeq>, Rc<ZOpSeq>, VecDeque<OpSeq>),
    InvalidText(String, CursorPositionText),
    Var(Identifier, CursorPositionText),
    Unit(CursorPosition),
    Int(i32, CursorPositionText),
    Bool(bool, CursorPosition),
    Str(String, CursorPositionText),
    // LetZpat(Rc<ZPat>, Option<Rc<Type>>, Rc<OpSeq>, Rc<OpSeq>),
    // LetZtyp(Rc<Pat>, Option<Rc<ZType>>, Rc<OpSeq>, Rc<OpSeq>),
    // LetZexp1(Rc<Pat>, Option<Rc<Type>>, Rc<ZOpSeq>, Rc<OpSeq>),
    // LetZexp2(Rc<Pat>, Option<Rc<Type>>, Rc<OpSeq>, Rc<ZOpSeq>),
    // FuncZarg(ZFuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<OpSeq>),
    // FuncZargs(
    //     FuncArg,
    //     VecDeque<FuncArg>,
    //     ZFuncArg,
    //     VecDeque<FuncArg>,
    //     Option<Rc<Type>>,
    //     Rc<OpSeq>,
    // ),
    // Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<OpSeq>),
    If(Rc<OpSeq>, Rc<OpSeq>, Rc<OpSeq>),
    Match(Rc<OpSeq>, Vec<Rule>),
}

pub type ZType = (Type, CursorPosition);

#[derive(Debug)]
pub enum CursorPosition {
    Before,
    After,
}

pub type CursorPositionText = usize;

// TODO make OpOpSeq (thing below is just a OpSeq) and Skel

#[derive(Debug)]
pub struct ZOpSeq {
    pub before: VecDeque<OpSeq>,
    current: OpSeqZToken,
    pub after: VecDeque<OpSeq>,
}

#[derive(Debug)]
pub enum OpSeqZToken {
    ZOperand(ZOperand),
    ZOperator(ZOperator),
    ZWhitespace(ZWhitespace),
}

#[derive(Debug)]
pub enum ZWhitespace {
    Space(CursorPosition),
    Newline(CursorPosition),
}

#[derive(Debug)]
pub enum ZOperator {
    InvalidText(String, CursorPositionText),
    Valid(BinOpcode, CursorPosition),
}

pub fn make_new_program() -> Rc<ZExp> {
    return Rc::new(ZExp::Hole(CursorPosition::Before));
}

#[derive(Debug)]
pub enum Action {
    Insert(char),
    Backspace,
    MoveLeft,
    MoveRight,
}

pub fn perform(action: Action, zexp: Rc<ZExp>) -> Rc<ZExp> {
    match action {
        Action::Insert(c) => match &*zexp.clone() {
            ZOperand::Hole(_) | ZOperand::Var(_, _) => perform_insert_operand(c, zexp),
            _ => panic!("todo case {:#?} not handled", zexp),
        },
        Action::Backspace => match &*zexp.clone() {
            ZOperand::Hole(_) | ZOperand::Var(_, _) => perform_backspace_operand(zexp),
            _ => panic!("todo case {:#?} not handled", zexp),
        },
        _ => panic!("todo case {:#?} not handled", action),
    }
}

fn perform_insert_operand(c: char, zexp: Rc<ZExp>) -> Rc<ZExp> {
    match &*zexp.clone() {
        ZOperand::Hole(_) => Rc::new(ZOperand::Var(String::from(c), 1)),
        ZOperand::Var(text, cursorpos) => {
            let mut new_text = text.clone();
            new_text.insert(*cursorpos, c);
            make_text(new_text, cursorpos + 1)
        }
        _ => panic!("todo case {:#?} not handled", zexp),
    }
}

fn perform_backspace_operand(zexp: Rc<ZExp>) -> Rc<ZExp> {
    match &*zexp.clone() {
        ZOperand::Hole(CursorPosition::After) => Rc::new(ZOperand::Hole(CursorPosition::Before)),
        ZOperand::Var(text, cursorpos) => {
            let mut new_text = text.clone();
            new_text.remove(*cursorpos - 1);
            make_text(new_text, cursorpos - 1)
        }
        _ => panic!("todo case {:#?} not handled", zexp),
    }
}

fn make_text(text: String, cursorpos: CursorPositionText) -> Rc<ZExp> {
    if (is_identifier(&text)) {
        Rc::new(ZOperand::Var(text, cursorpos))
    } else {
        Rc::new(ZOperand::InvalidText(text, cursorpos))
    }
}

fn is_identifier(text: &str) -> bool {
    let re = Regex::new(r"[a-zA-Z_.][.a-zA-Z_0-9']*(\.:[.+/*=-]+)?").unwrap();
    return re.is_match(text);
}
