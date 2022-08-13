// use operators::BinOpcode;
// use regex::Regex;
// use std::collections::VecDeque;
// use std::rc::Rc;
// use types::Type;

// pub type Identifier = String;
// pub type FuncArg = (Identifier, Option<Rc<Type>>);

// #[derive(Debug)]
// pub struct Exp(Operand);

// pub type Pat = (); // TODO

// pub type Rule = (Pat, Exp);

// #[derive(Debug)]
// pub enum Operand {
//     Hole,
//     InvalidText(String),
//     Var(Identifier),
//     Unit,
//     Int(i32),
//     Bool(bool),
//     Str(String),

//     Block(Rc<VecDeque<OpSeq>>),
//     // Let(Rc<Pat>, Option<Rc<Type>>, Rc<OpSeq>, Rc<OpSeq>),
//     // Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<OpSeq>),
//     If(Rc<OpSeq>, Rc<OpSeq>, Rc<OpSeq>),
//     Match(Rc<OpSeq>, Vec<Rule>),
// }

// pub type OpSeq = VecDeque<OpSeqToken>;

// #[derive(Debug)]
// pub enum OpSeqToken {
//     Operand(Operand),
//     Operator(Operator),
//     Space(Whitespace),
// }

// #[derive(Debug)]
// pub enum Whitespace {
//     Space,
//     Newline,
// }

// #[derive(Debug)]
// pub enum Operator {
//     InvalidText(String),
//     Valid(BinOpcode),
// }

// pub type ZPat = (); // TODO

// // pub type ZRuleL = (ZPat, Exp);

// // pub type ZRuleR = (Pat, ZExp);

// #[derive(Debug)]
// pub enum ZOperand {
//     Hole(CursorPosition),
//     Block(Rc<VecDeque<OpSeq>>, Rc<ZOpSeq>, Rc<VecDeque<OpSeq>>),
//     InvalidText(String, CursorPositionText),
//     Var(Identifier, CursorPositionText),
//     Unit(CursorPosition),
//     Int(i32, CursorPositionText),
//     Bool(bool, CursorPosition),
//     Str(String, CursorPositionText),
//     // LetZpat(Rc<ZPat>, Option<Rc<Type>>, Rc<OpSeq>, Rc<OpSeq>),
//     // LetZtyp(Rc<Pat>, Option<Rc<ZType>>, Rc<OpSeq>, Rc<OpSeq>),
//     // LetZexp1(Rc<Pat>, Option<Rc<Type>>, Rc<ZOpSeq>, Rc<OpSeq>),
//     // LetZexp2(Rc<Pat>, Option<Rc<Type>>, Rc<OpSeq>, Rc<ZOpSeq>),
//     // FuncZarg(ZFuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<OpSeq>),
//     // FuncZargs(
//     //     FuncArg,
//     //     VecDeque<FuncArg>,
//     //     ZFuncArg,
//     //     VecDeque<FuncArg>,
//     //     Option<Rc<Type>>,
//     //     Rc<OpSeq>,
//     // ),
//     // Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<OpSeq>),
//     If(Rc<OpSeq>, Rc<OpSeq>, Rc<OpSeq>),
//     Match(Rc<OpSeq>, Vec<Rule>),
// }

// pub type ZType = (Type, CursorPosition);

// #[derive(Debug)]
// pub enum CursorPosition {
//     Before,
//     After,
// }

// pub type CursorPositionText = usize;

// // TODO make OpOpSeq (thing below is just a OpSeq) and Skel

// #[derive(Debug)]
// pub struct ZOpSeq {
//     pub before: Rc<VecDeque<OpSeq>>,
//     current: Rc<OpSeqZToken>,
//     pub after: Rc<VecDeque<OpSeq>>,
// }

// #[derive(Debug)]
// pub enum OpSeqZToken {
//     ZOperand(ZOperand),
//     ZOperator(ZOperator),
//     ZWhitespace(ZWhitespace),
// }

// #[derive(Debug)]
// pub enum ZWhitespace {
//     Space(CursorPosition),
//     Newline(CursorPosition),
// }

// #[derive(Debug)]
// pub enum ZOperator {
//     InvalidText(String, CursorPositionText),
//     Valid(BinOpcode, CursorPosition),
// }

// macro_rules! vecdeque {
//     () => (
//         VecDeque::new()
//     );
//     ($elem:expr; $n:expr) => (
//         $crate::vec::from_elem($elem, $n).to_iter().collect()
//     );
//     ($($x:expr),*) => (
//         $crate::slice::into_vec(box [$($x),*]).to_iter().collect()
//     );
//     ($($x:expr,)*) => (vec![$($x),*].to_iter().collect())
// }

// pub fn make_new_program() -> Rc<ZOperand> {
//     let hole = ZOperand::Hole(CursorPosition::Before);
//     let zopseq = Rc::new(ZOpSeq {
//         before: Rc::new(vecdeque![]),
//         current: Rc::new(OpSeqZToken::ZOperand(hole)),
//         after: Rc::new(vecdeque![]),
//     });
//     let block = ZOperand::Block(Rc::new(vecdeque![]), zopseq, Rc::new(vecdeque![]));
//     return Rc::new(block);
// }

// #[derive(Debug)]
// pub enum Action {
//     Insert(char),
//     Backspace,
//     MoveLeft,
//     MoveRight,
// }

// pub fn perform(action: Action, zexp: Rc<ZOperand>) -> Rc<ZOperand> {
//     match action {
//         Action::Insert(c) => match &*zexp.clone() {
//             ZOperand::Block(before, zopseq, after) => Rc::new(ZOperand::Block(
//                 before.clone(),
//                 perform_zopseq(action, zopseq.clone()),
//                 after.clone(),
//             )),
//             ZOperand::Hole(_) | ZOperand::Var(_, _) => perform_insert_operand(c, zexp),
//             _ => panic!("todo case {:#?} not handled", zexp),
//         },
//         Action::Backspace => match &*zexp.clone() {
//             ZOperand::Hole(_) | ZOperand::Var(_, _) => perform_backspace_operand(zexp),
//             _ => panic!("todo case {:#?} not handled", zexp),
//         },
//         _ => panic!("todo case {:#?} not handled", action),
//     }
// }

// pub fn perform_zopseq(action: Action, zopseq: Rc<ZOpSeq>) -> Rc<ZOpSeq> {
//     match action {
//         _ => {
//             let ZOpSeq {
//                 before,
//                 current,
//                 after,
//             } = *zopseq;
//             match &*current.clone() {
//                 ZOperand(zoperand) => Rc::new(ZOpSeq {
//                     before,
//                     current: Rc::new(OpSeqZToken::ZOperand(perform(action, zoperand))),
//                     after,
//                 }),
//                 _ => panic!("todo case {:#?} not handled", current),
//             }
//         }
//     }
// }

// fn perform_insert_operand(c: char, zexp: Rc<ZOperand>) -> Rc<ZOperand> {
//     match &*zexp.clone() {
//         ZOperand::Hole(_) => Rc::new(ZOperand::Var(String::from(c), 1)),
//         ZOperand::Var(text, cursorpos) => {
//             let mut new_text = text.clone();
//             new_text.insert(*cursorpos, c);
//             make_text_operand(new_text, cursorpos + 1)
//         }
//         _ => panic!("todo case {:#?} not handled", zexp),
//     }
// }

// fn perform_backspace_operand(zexp: Rc<ZOperand>) -> Rc<ZOperand> {
//     match &*zexp.clone() {
//         ZOperand::Hole(CursorPosition::After) => Rc::new(ZOperand::Hole(CursorPosition::Before)),
//         ZOperand::Var(text, cursorpos) => {
//             let mut new_text = text.clone();
//             new_text.remove(*cursorpos - 1);
//             make_text_operand(new_text, cursorpos - 1)
//         }
//         _ => panic!("todo case {:#?} not handled", zexp),
//     }
// }

// fn make_text_operand(text: String, cursorpos: CursorPositionText) -> Rc<ZOperand> {
//     if is_identifier(&text) {
//         Rc::new(ZOperand::Var(text, cursorpos))
//     } else {
//         Rc::new(ZOperand::InvalidText(text, cursorpos))
//     }
// }

// fn is_identifier(text: &str) -> bool {
//     let re = Regex::new(r"[a-zA-Z_.][.a-zA-Z_0-9']*(\.:[.+/*=-]+)?").unwrap();
//     return re.is_match(text);
// }
