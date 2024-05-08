use std::{cell::RefCell, rc::Rc};

use abra_core::*;

#[test]
fn smoke() {
    let src = "2";
    assert!(compile::<side_effects::DefaultEffects>(vec![SourceFile {
        name: "test.abra".to_owned(),
        contents: src.to_owned(),
    },])
    .is_ok());
}

#[test]
fn smoke2() {
    let src = r#""hello" & "world""#;
    assert!(compile::<side_effects::DefaultEffects>(vec![SourceFile {
        name: "test.abra".to_owned(),
        contents: src.to_owned(),
    },])
    .is_ok());
}

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

#[test]
fn while_loop_mutation() {
    let (val, rt) = run("let mutable i = 0
    while i < 10 {
        i <- i + 1
    }
    i")
    .unwrap();
    assert_eq!(val, rt.make_int(10));
}

#[test]
fn struct_field_mutation() {
    let (val, rt) = run("
        type coord = {
            x: int,
            y: int
        }

        let c = coord(2, 3)

        c.x <- c.x * 5
        c.x
        ")
    .unwrap();
    assert_eq!(val, rt.make_int(10));
}

#[test]
fn transform_list_then_sum() {
    let src = r#"func fibonacci(n) {
        match n {
            0 -> 0
            1 -> 1
            _ -> fibonacci(n-1) + fibonacci(n-2)
        }
    }

    let list = range(0,9)
    println("numbers: ")
    println(list)

    let list = map(list, fibonacci)
    println("fibonacci: ")
    println(list)

    let list = map(list, x -> x ^ 3)
    println("cubed: ")
    println(list)

    let list = filter(list, x -> x mod 2 = 1)
    println("only odds: ")
    println(list)

    let list = map(list, x -> to_float(x) * 3.14)
    println("times pi: ")
    println(list)

    print(newline)
    print("they add up to: ")
    let n = sumf(list)
    println(sumf(list))
    n
    "#;
    let (val, _) = run(src).unwrap();
    assert!(val.get_float() - 36461.68 < 0.001);
}

fn handler_inner(
    code: EffectCode,
    args: Vec<Rc<eval_tree::Expr>>,
    output: Rc<RefCell<String>>,
    inputs: Rc<RefCell<Vec<&str>>>,
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
            let mut inputs = inputs.borrow_mut();
            let input = inputs.pop().unwrap();
            eval_tree::Expr::from(input.trim()).into()
        }
    }
}

#[test]
fn hello_world() {
    let output_str = Rc::new(RefCell::new("".to_owned()));
    let inputs = Rc::new(RefCell::new(vec![]));
    let _ = run_with_handler::<side_effects::DefaultEffects>(
        r#"println("hello world")"#,
        Box::new(|code, args| handler_inner(code, args, output_str.clone(), inputs.clone())),
    )
    .unwrap();
    assert_eq!(*output_str.borrow(), "hello world\n");
}

#[test]
fn readline() {
    let output_str = Rc::new(RefCell::new("".to_owned()));
    let inputs = Rc::new(RefCell::new(vec!["world", "hello"]));
    let src = r#"let s = read()
println(s)"#;
    let _ = run_with_handler::<side_effects::DefaultEffects>(
        src,
        Box::new(|code, args| handler_inner(code, args, output_str.clone(), inputs.clone())),
    )
    .unwrap();
    assert_eq!(*output_str.borrow(), "hello\n");
}

#[test]
fn addition_bad() {
    let src = "2 + true";
    assert!(compile::<side_effects::DefaultEffects>(source_files_single(src)).is_err());
}

#[test]
fn map_bad() {
    let src = r#"let list = range(0,9)
 map(list, x -> x & "hello")"#;
    assert!(compile::<side_effects::DefaultEffects>(source_files_single(src)).is_err());
}
