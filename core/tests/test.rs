use std::{cell::RefCell, rc::Rc};

use abra_core::*;

#[test]
fn addition() {
    let (val, rt) = run("2+2").unwrap();
    assert_eq!(val, rt.make_int(4));
}

#[test]
fn arithmetic() {
    let (val, rt) = run("2 + 3 * 4 / 3").unwrap();
    assert_eq!(val, rt.make_int(6));
}

#[test]
fn fib() {
    let (val, rt) = run("func fibonacci(n) {
        match n {
            0 -> 0
            1 -> 1
            _ -> fibonacci(n-1) + fibonacci(n-2)
        }
    }
    fibonacci(6)")
    .unwrap();
    assert_eq!(val, rt.make_int(8));
}

// TODO: why eval_tree is namespace for EffectCode ?
fn handler_inner(
    code: eval_tree::EffectCode,
    args: Vec<Rc<eval_tree::Expr>>,
    output: Rc<RefCell<String>>,
) -> Rc<eval_tree::Expr> {
    let effect = &side_effects::DEFAULT_EFFECT_LIST[code as usize];
    match effect {
        side_effects::DefaultEffects::PrintString => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                output.borrow_mut().push_str(string);
                eval_tree::Expr::from(()).into()
            }
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        side_effects::DefaultEffects::Read => {
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).unwrap();
            eval_tree::Expr::from(input.trim()).into()
        }
    }
}

#[test]
fn hello_world() {
    let output_str = Rc::new(RefCell::new("".to_owned()));
    let _ = run_with_handler::<side_effects::DefaultEffects>(
        r#"println("hello world")"#,
        Box::new(|code, args| handler_inner(code, args, output_str.clone())),
    )
    .unwrap();
    assert_eq!(*output_str.borrow(), "hello world\n");
}
