/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::MockFileProvider;
use abra_core::compile_bytecode;
use abra_core::vm::Vm;
use abra_core::vm::VmStatus;
use std::collections::HashMap;
use std::path::PathBuf;

use crate::utils::unwrap_or_panic;

#[test]
fn arithmetic() {
    let src = r#"
fn sub(x, y) {
  x - y
}
let x = 3
let y = 4
let z = sub(x, y)
let h = sub(z, 1)
h
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), -2);
    println!("result is {}", top.get_int(&vm).unwrap());
}

#[test]
fn tuples() {
    let src = r#"
fn mk_pair(a) {
  (a, a)
}
let n = 3
let p = mk_pair(n)
let (x, y) = p
x + y
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
    println!("result is {}", top.get_int(&vm).unwrap());
}

#[test]
fn if_else() {
    let src = r#"
if false {
  3
} else {
  4
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 4);
    println!("result is {}", top.get_int(&vm).unwrap());
}

#[test]
fn just_if() {
    let src = r#"
var x = 3
if true {
    x <- x + x
}
x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
    println!("result is {}", top.get_int(&vm).unwrap());
}

#[test]
fn print_string() {
    let src = r#"
print_string("hello world")
5
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "hello world");
    vm.pop().unwrap();
    vm.push_nil();
    vm.clear_pending_host_func();
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 5);
}

#[test]
fn struct_assign_and_access1() {
    let src = r#"
type person = {
    name: string
    age: int
}
let x = person("Alice", 30)
x.name <- "Bob"
x.age <- 2 * 3 * 6
x.name
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "Bob");
}

#[test]
fn struct_assign_and_access2() {
    let src = r#"
type person = {
    name: string
    age: int
}
let x = person("Alice", 30)
x.name <- "Bob"
x.age <- 2 * 3 * 6
x.age
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 36);
}

#[test]
fn array_assign_and_access() {
    let src = r#"
let arr = [ 1, 2, 3, 4 ]
arr[2]
arr[2] <- 33
arr[2]
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 33);
}

#[test]
fn nested_struct_and_array_assignment() {
    let src = r#"
type Snake = {
    body: array<Point>
    direction: int
}
type Point = {
    x: int
    y: int
}

let snake = Snake([Point(10,10)], 0)
let body = snake.body
let first = body[0]
first.x <- 20
let body = snake.body
let first = body[0]
first.x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 20);
}

#[test]
fn nested_struct_and_array_assignment2() {
    let src = r#"
type Snake = {
    body: array<Point>
    direction: int
}
type Point = {
    x: int
    y: int
}

let snake = Snake([Point(10,10)], 0)
snake.body[0].x <- 20
snake.body[0].x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 20);
}

#[test]
fn match_int() {
    let src = r#"
let n = 1
match n {
  | 0 -> 0
  | 1 -> 1
  | _ -> 2
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 1);
}

#[test]
fn match_int_wild() {
    let src = r#"
let n = 42
match n {
  | 0 -> 0
  | 1 -> 1
  | _ -> 99
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 99);
}

#[test]
fn match_two_bools() {
    let src = r#"
let b = true
let one = match b {
  | true -> 1
  | false -> 2
}
let b = false
let two = match b {
  | true -> 1
  | false -> 2
}
let sum = one + two
sum
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 3);
}

#[test]
fn match_pair_first_case() {
    let src = r#"
let triplet = (1, 1)
match triplet {
    | (1, 1) -> 100
    | (1, 2) -> 101
    | _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 100);
}

#[test]
fn match_pair_second_case() {
    let src = r#"
let pair = (1, 2)
match pair {
    | (1, 1) -> 100
    | (1, 2) -> 101
    | _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 101);
}

#[test]
fn match_pair_wild() {
    let src = r#"
let pair = (2, 1)
match pair {
    | (1, 1) -> 100
    | (1, 2) -> 101
    | _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 102);
}

#[test]
fn match_quintuple_booleans() {
    let src = r#"
let quintuple = (true, false, true, true, false)
match quintuple {
    | (true, false, true, true, true) -> 100
    | (true, false, true, true, false) -> 101
    | _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 101);
}

#[test]
fn match_nested_tuple() {
    let src = r#"
let triplet = (1, (2, 3), 4)
match triplet {
    | (1, (2, 88), 4) -> 100
    | (1, (2, 3), 4) -> 101
    | _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 101);
}

#[test]
fn pattern_tuples_binding() {
    let src = r#"
let xs = (1, (2, 3))
match xs {
    | (x, (y, z)) -> y
}"#;
    //     let src = r#"
    // let xs = list.nil
    // match xs {
    //     list.cons(x, _) -> 9
    //     list.nil -> 100
    // }"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 2);
}

#[test]
fn match_cons_binding() {
    let src = r#"
let xs = list.cons(23, list.nil)
match xs {
    | list.nil -> 100
    | list.cons(x, _) -> x
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 23);
}

#[test]
fn match_cons_binding_nested() {
    let src = r#"
let xs = list.cons(1, list.cons(2, list.nil))
match xs {
    | list.nil -> 100
    | list.cons(_, list.cons(x, list.nil)) -> x
    | _ -> 101
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 2);
}

#[test]
fn recursive_identity_function() {
    let src = r#"
fn r(n) {
    match n {
        | 0 -> 0
        | _ -> 1 + r(n-1)
    }
}
r(2)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 2);
}

#[test]
fn fib_naive() {
    let src = r#"
fn fib(n) {
    match n {
        | 0 -> 0
        | 1 -> 1
        | _ -> fib(n-1) + fib(n-2)
    }
}
fib(10)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 55);
}

#[test]
fn lambda1() {
    let src = r#"
let double = x -> x + x
double(5)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 10);
}

#[test]
fn lambda2() {
    let src = r#"
let add = (x, y) -> x + y
add(2, 3)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 5);
}

#[test]
fn sqrt_float() {
    let src = r#"
let f = 4.0
let g = sqrt_float(f)
g
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_float(&vm).unwrap(), 2.0);
}

#[test]
fn array_append() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
append(arr, 6)
arr[5]
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
}

#[test]
fn array_len() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
len(arr)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 5);
}

#[test]
fn list_literal_head() {
    let src = r#"
match [| 1, 2, 3 |] {
  | list.nil -> 0
  | list.cons(x, _) -> x
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 1);
}

#[test]
fn list_literal_total() {
    let src = r#"
let xs = [| 1, 2, 3 |]

fn total(xs) {
    match xs {
      | list.cons(x, xs) -> x + total(xs)
      | list.nil -> 0
    }
}

total(xs)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
}

#[test]
fn parametric_polymorphic_func() {
    let src = r#"
let nums = [| 1, 2, 3 |]
let bools = [| true, false, true, true, false |]

fn list_len(xs: list<'a>) {
    match xs {
      | list.cons(_, xs) -> 1 + list_len(xs)
      | list.nil -> 0
    }
}

list_len(nums) + list_len(bools)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 8);
}

#[test]
fn concat_strings() {
    let src = r#"
let s = "hello " & "world"
s
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "hello world");
}

#[test]
fn monomorphize_to_string_int() {
    let src = r#"
str(123)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "123");
}

#[test]
fn monomorphize_to_string_float() {
    let src = r#"
str(123)
str(123.456)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "123.456");
}

#[test]
fn monomorphize_to_string_tuple_ints() {
    let src = r#"
let nums = (1, 2, 3)
str(nums)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "(1, 2, 3)");
}

#[test]
fn local_in_while_scope() {
    let src = r#"
    var x = 5
    while x > 0 {
        let tmp = x
        x <- tmp - 1
    }
    5
    "#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 5);
}

#[test]
fn continue_and_break() {
    let src = r#"
    var i = 0
    while true {
        if i < 10 {
            i <- i + 1
            continue
        }
        break
    }
    i
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 10);
}

#[test]
fn early_return() {
    let src = r#"
fn fib(n) {
    if n < 2 {
      return n
    }
    return fib(n - 2) + fib(n - 1)
  }
  
fib(10)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 55);
}

#[test]
fn garbage_collection_once() {
    let src = r#"
var i = 0
var x = 3
while i < 10000 {
    let p = (1, 2, 3)
    let (a, b, c) = p
    x <- a + b + c
    i <- i + 1
}
x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    while !vm.is_done() {
        vm.run_n_steps(1);
    }
    vm.gc();
    assert!(vm.nbytes() < 10000);
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
}

#[test]
fn garbage_collection_repeated() {
    let src = r#"
var i = 0
var x = 3
while i < 10000 {
    let p = (1, 2, 3)
    let (a, b, c) = p
    x <- a + b + c
    i <- i + 1
}
x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    while !vm.is_done() {
        vm.run_n_steps(1);
        vm.gc();
        assert!(vm.nbytes() < 10000);
    }
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
}

#[test]
fn entry_point() {
    let src = r#"
fn my_entry_point() {
    print_string("hello world")
}

5
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::with_entry_point(program, "main.my_entry_point".to_owned());
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "hello world");
    vm.pop().unwrap();
    vm.push_nil();
    vm.clear_pending_host_func();
    vm.run();
}

#[test]
fn entry_point_with_args() {
    let src = r#"
fn my_entry_point(x, y) {
    x + y
}

my_entry_point(5, 6)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::with_entry_point(program, "main.my_entry_point".to_owned());
    vm.push_int(2);
    vm.push_int(3);
    vm.increment_stack_base(2);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 5);
}

#[test]
fn namespaced_files() {
    let util = r#"
fn foo(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util

fn bar(x: 'a) -> 'a {
  x
}

foo(2, 2)
"#;
    let mut files: HashMap<PathBuf, String> = HashMap::new();
    files.insert("main.abra".into(), main.into());
    files.insert("util.abra".into(), util.into());
    let file_provider = MockFileProvider::new(files);

    let program = compile_bytecode("main.abra", file_provider);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 4);
    println!("result is {}", top.get_int(&vm).unwrap());
}

#[test]
fn format_append() {
    let src = r#"
format_append(format_append(123, true), false)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "123truefalse");
}

#[test]
fn ampersand() {
    let src = r#"
123 & true & false
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_string(&vm).unwrap(), "123truefalse");
}

#[test]
fn comments() {
    let src = r#"
// single-line comment
2 + 2 // => 4
/* multi-line
comment */
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 4);
}

#[test]
fn host_function() {
    let src = r#"
host fn do_stuff() -> int

do_stuff()
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let status = vm.status();
    let VmStatus::PendingHostFunc(0) = status else {
        panic!()
    };
}

#[test]
fn host_function2() {
    let src = r#"
host fn do_stuff() -> int
host fn do_stuff2() -> int

let x = do_stuff2()
x + x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let status = vm.status();
    let VmStatus::PendingHostFunc(1) = status else {
        panic!()
    };
    vm.push_int(3);
    vm.clear_pending_host_func();
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 6);
}
