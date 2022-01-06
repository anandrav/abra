use operators::BinOpcode::*;
use operators::*;
use side_effects::Output::*;
use side_effects::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use typed_tree::Expr::*;
use typed_tree::*;

pub struct Effects {
    outputs: Vec<Output>,
}

impl Effects {
    pub fn empty() -> Effects {
        Effects {
            outputs: Vec::new(),
        }
    }
}

pub struct Environment {
    vars: HashMap<Identifier, Rc<Expr>>,
    enclosing: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn new(enclosing: Option<Rc<RefCell<Environment>>>) -> Self {
        Self {
            vars: HashMap::new(),
            enclosing: enclosing,
        }
    }

    pub fn lookup(&self, id: &Identifier) -> Option<Rc<Expr>> {
        match self.vars.get(id) {
            Some(expr) => Some(expr.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, id: &Identifier, expr: Rc<Expr>) {
        self.vars.insert(id.clone(), expr.clone());
    }
}

fn perform_op(val1: Rc<Expr>, op: BinOpcode, val2: Rc<Expr>) -> Rc<Expr> {
    match op {
        Add => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 + i2)),
            _ => panic!("one or more operands of Add are not Ints"),
        },
        Subtract => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 - i2)),
            _ => panic!("one or more operands of Subtract are not Ints"),
        },
        Multiply => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 * i2)),
            _ => panic!("one or more operands of Multiply are not Ints"),
        },
        Equals => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 == i2)),
            (Bool(b1), Bool(b2)) => Rc::new(Bool(b1 == b2)),
            _ => panic!("can only compare values which are both Ints or both Bools"),
        },
        GreaterThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 > i2)),
            _ => panic!("one or more operands of GreaterThan are not Ints"),
        },
        GreaterThanOrEquals => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 >= i2)),
            _ => panic!("one or more operands of GreaterThanOrEquals are not Ints"),
        },
        LessThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 < i2)),
            _ => panic!("one or more operands of LessThan are not Ints"),
        },
        LessThanOrEquals => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 <= i2)),
            _ => panic!("one or more operands of LessThanOrEquals are not Ints"),
        },
        // FuncAp => match &*val1 {
        //     Func(id, _, _, body) => {
        //         let new_env = Rc::new(RefCell::new(Environment::new(Some(env))));
        //         new_env.borrow_mut().extend(&id, val2.clone());
        //         eval(body.clone(), new_env, effects)
        //     }
        //     _ => panic!("left operand of function application is not a function!"),
        // },
        _ => panic!("todo"),
    }
}

pub fn eval(expr: Rc<Expr>, env: Rc<RefCell<Environment>>, effects: &Effects) -> Rc<Expr> {
    match &*expr {
        Var(id) => {
            let result = env.borrow_mut().lookup(id);
            match result {
                None => panic!("No value for variable with id: {}", id),
                Some(val) => val,
            }
        }
        Unit | Int(_) | Bool(_) | Func(_, _, _, _) => expr.clone(),
        BinOp(expr1, op, expr2) => {
            let val1 = eval(expr1.clone(), env.clone(), effects);
            let val2 = eval(expr2.clone(), env.clone(), effects);
            perform_op(val1, *op, val2)
        }
        Let(pat, _, expr1, expr2) => match &*pat.clone() {
            Pat::Var(id) => {
                let val = eval(expr1.clone(), env.clone(), effects);
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env))));
                new_env.borrow_mut().extend(&id, val);
                eval(expr2.clone(), new_env, effects)
            }
        },
        FuncAp(expr1, expr2) => {
            let val1 = eval(expr1.clone(), env.clone(), effects);
            let val2 = eval(expr2.clone(), env.clone(), effects);
            let (id, body) = match &*val1.clone() {
                Func(id, _, _, body) => (id.clone(), body.clone()),
                _ => panic!("Left expression of FuncAp is not a function"),
            };
            println!(
                "before substitution, val2 is {:#?} and id is {} and body is {:#?}",
                val2, id, body
            );
            let new_env = Rc::new(RefCell::new(Environment::new(Some(env))));
            new_env.borrow_mut().extend(&id, val2.clone());
            eval(body, new_env, effects)
        }
        If(expr1, expr2, expr3) => {
            let val1 = eval(expr1.clone(), env.clone(), effects);
            match &*val1 {
                Bool(true) => eval(expr2.clone(), env.clone(), effects),
                Bool(false) => eval(expr3.clone(), env.clone(), effects),
                _ => panic!("If expression clause did not evaluate to a bool"),
            }
        }
    }
}
