/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::Location;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Func(u32);

impl Func {
    fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("too many MIR functions"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for Func {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Block(u32);

impl Block {
    fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("too many MIR blocks"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "block{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Inst(u32);

impl Inst {
    fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("too many MIR instructions"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for Inst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "inst{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Value(u32);

impl Value {
    fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("too many MIR values"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Ty {
    Void,
    Never,
    Bool,
    Int,
    Float,
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::Never => write!(f, "never"),
            Ty::Bool => write!(f, "bool"),
            Ty::Int => write!(f, "int"),
            Ty::Float => write!(f, "float"),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Program {
    functions: Vec<Function>,
}

impl Program {
    pub(crate) fn push_function(&mut self, function: Function) -> Func {
        let handle = Func::new(self.functions.len());
        self.functions.push(function);
        handle
    }

    pub(crate) fn functions(&self) -> impl ExactSizeIterator<Item = Func> + '_ {
        (0..self.functions.len()).map(Func::new)
    }

    pub(crate) fn function(&self, function: Func) -> &Function {
        &self.functions[function.index()]
    }
}

#[derive(Debug)]
pub(crate) struct Function {
    return_ty: Ty,
    blocks: Vec<BlockData>,
    insts: Vec<InstData>,
    value_types: Vec<Ty>,
}

impl Function {
    pub(crate) fn entry_block(&self) -> Block {
        Block::new(0)
    }

    pub(crate) fn return_type(&self) -> &Ty {
        &self.return_ty
    }

    pub(crate) fn blocks(&self) -> impl ExactSizeIterator<Item = Block> + '_ {
        (0..self.blocks.len()).map(Block::new)
    }

    pub(crate) fn block(&self, block: Block) -> &BlockData {
        &self.blocks[block.index()]
    }

    pub(crate) fn inst(&self, inst: Inst) -> &InstData {
        &self.insts[inst.index()]
    }

    pub(crate) fn value_type(&self, value: Value) -> &Ty {
        &self.value_types[value.index()]
    }

    pub(crate) fn instructions(&self, block: Block) -> impl Iterator<Item = Inst> + '_ {
        self.block(block).insts.iter().copied()
    }

    fn verify(&self) {
        for block in self.blocks() {
            let terminator = self
                .block(block)
                .terminator
                .as_ref()
                .unwrap_or_else(|| panic!("{block} has no terminator"));
            match &terminator.kind {
                TerminatorKind::Jump {
                    destination,
                    arguments,
                } => self.verify_edge(block, *destination, arguments),
                TerminatorKind::Branch {
                    condition,
                    then_block,
                    else_block,
                } => {
                    assert_eq!(
                        self.value_type(*condition),
                        &Ty::Bool,
                        "{block} has a non-boolean branch condition"
                    );
                    self.verify_edge(block, *then_block, &[]);
                    self.verify_edge(block, *else_block, &[]);
                }
                TerminatorKind::Return(value) => {
                    let found = value
                        .map(|value| self.value_type(value))
                        .unwrap_or(&Ty::Void);
                    assert_eq!(found, &self.return_ty, "{block} returns the wrong type");
                }
            }
        }
    }

    fn verify_edge(&self, from: Block, destination: Block, arguments: &[Value]) {
        let parameters = &self.block(destination).params;
        assert_eq!(
            arguments.len(),
            parameters.len(),
            "argument count from {from} does not match parameters of {destination}"
        );
        for (argument, parameter) in arguments.iter().zip(parameters) {
            assert_eq!(
                self.value_type(*argument),
                self.value_type(*parameter),
                "argument type from {from} does not match parameter of {destination}"
            );
        }
    }
}

#[derive(Debug)]
pub(crate) struct BlockData {
    params: Vec<Value>,
    insts: Vec<Inst>,
    terminator: Option<Terminator>,
}

impl BlockData {
    pub(crate) fn params(&self) -> &[Value] {
        &self.params
    }

    pub(crate) fn terminator(&self) -> Option<&Terminator> {
        self.terminator.as_ref()
    }
}

#[derive(Debug)]
pub(crate) struct InstData {
    kind: InstKind,
    result: Value,
    span: Location,
}

impl InstData {
    pub(crate) fn kind(&self) -> &InstKind {
        &self.kind
    }

    pub(crate) fn result(&self) -> Value {
        self.result
    }

    pub(crate) fn span(&self) -> &Location {
        &self.span
    }
}

#[derive(Debug)]
pub(crate) struct Terminator {
    kind: TerminatorKind,
    span: Location,
}

impl Terminator {
    pub(crate) fn kind(&self) -> &TerminatorKind {
        &self.kind
    }

    pub(crate) fn span(&self) -> &Location {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TerminatorKind {
    Jump {
        destination: Block,
        arguments: Vec<Value>,
    },
    Branch {
        condition: Value,
        then_block: Block,
        else_block: Block,
    },
    Return(Option<Value>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InstKind {
    BoolConst(bool),
    IntConst(i64),
    FloatConst(String),
    Unary {
        op: UnaryOp,
        operand: Value,
    },
    Binary {
        op: BinaryOp,
        left: Value,
        right: Value,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnaryOp {
    BoolNot,
    IntNeg,
    FloatNeg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinaryOp {
    IntAdd,
    IntSubtract,
    IntMultiply,
    IntDivide,
    IntModulo,
    IntPow,
    FloatAdd,
    FloatSubtract,
    FloatMultiply,
    FloatDivide,
    FloatPow,
    IntEqual,
    IntNotEqual,
    IntLessThan,
    IntLessThanOrEqual,
    IntGreaterThan,
    IntGreaterThanOrEqual,
    FloatEqual,
    FloatNotEqual,
    FloatLessThan,
    FloatLessThanOrEqual,
    FloatGreaterThan,
    FloatGreaterThanOrEqual,
    BoolEqual,
    BoolNotEqual,
}

pub(crate) struct FunctionBuilder {
    function: Function,
}

impl FunctionBuilder {
    pub(crate) fn new(return_ty: Ty) -> Self {
        Self {
            function: Function {
                return_ty,
                blocks: vec![BlockData {
                    params: vec![],
                    insts: vec![],
                    terminator: None,
                }],
                insts: vec![],
                value_types: vec![],
            },
        }
    }

    pub(crate) fn entry_block(&self) -> Block {
        self.function.entry_block()
    }

    pub(crate) fn create_block(&mut self) -> Block {
        let block = Block::new(self.function.blocks.len());
        self.function.blocks.push(BlockData {
            params: vec![],
            insts: vec![],
            terminator: None,
        });
        block
    }

    pub(crate) fn append_block_param(&mut self, block: Block, ty: Ty) -> Value {
        let value = self.create_value(ty);
        self.function.blocks[block.index()].params.push(value);
        value
    }

    pub(crate) fn append_inst(
        &mut self,
        block: Block,
        kind: InstKind,
        ty: Ty,
        span: Location,
    ) -> Value {
        let inst = Inst::new(self.function.insts.len());
        let result = self.create_value(ty);
        self.function.insts.push(InstData { kind, result, span });
        self.function.blocks[block.index()].insts.push(inst);
        result
    }

    pub(crate) fn jump(
        &mut self,
        block: Block,
        destination: Block,
        arguments: Vec<Value>,
        span: Location,
    ) {
        self.terminate(
            block,
            TerminatorKind::Jump {
                destination,
                arguments,
            },
            span,
        );
    }

    pub(crate) fn branch(
        &mut self,
        block: Block,
        condition: Value,
        then_block: Block,
        else_block: Block,
        span: Location,
    ) {
        self.terminate(
            block,
            TerminatorKind::Branch {
                condition,
                then_block,
                else_block,
            },
            span,
        );
    }

    pub(crate) fn return_(&mut self, block: Block, value: Option<Value>, span: Location) {
        self.terminate(block, TerminatorKind::Return(value), span);
    }

    pub(crate) fn value_type(&self, value: Value) -> &Ty {
        self.function.value_type(value)
    }

    pub(crate) fn return_type(&self) -> &Ty {
        self.function.return_type()
    }

    pub(crate) fn finish(self) -> Function {
        self.function.verify();
        self.function
    }

    fn create_value(&mut self, ty: Ty) -> Value {
        let value = Value::new(self.function.value_types.len());
        self.function.value_types.push(ty);
        value
    }

    fn terminate(&mut self, block: Block, kind: TerminatorKind, span: Location) {
        let previous = self.function.blocks[block.index()]
            .terminator
            .replace(Terminator { kind, span });
        assert!(previous.is_none());
    }
}
