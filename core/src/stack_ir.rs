use crate::vm::AbraInt;

type Label = String;

#[derive(Debug)]
enum Instr {
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Return,
    PushBool(bool),
    PushInt(AbraInt),
    Jump(Label),
    JumpIfTrue(Label),
    Call(Label),
}
