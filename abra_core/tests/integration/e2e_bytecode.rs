/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::helper::unwrap_or_panic;
use abra_core::MockFileProvider;
use abra_core::compile_bytecode;
use abra_core::vm::Vm;
use abra_core::vm::VmStatus;
use std::collections::HashMap;
use std::path::PathBuf;

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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), -2);
}

#[test]
fn more_arithmetic() {
    let src = r#"
let a = 2
let b = a + 3
let c = b - 2
let d = c * 3
let e = d / 3
let f = e ^ 3
let g = f mod 5
g
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 2);
}

#[test]
fn more_arithmetic_floats() {
    let src = r#"
let a = 2.0
let b = a + 3.0
let c = b - 2.0
let d = c * 3.0
let e = d / 3.0
let f = e ^ 3.0
f
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_float(&vm), 27.0);
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6);
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 4);
}

#[test]
fn if_else_no_result() {
    let src = r#"
var x = 0
if false {
  x = 1
} else {
  x = 2
}
x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 2);
}

#[test]
fn just_if() {
    let src = r#"
var x = 3
if true {
    x = x + x
}
x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6);
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
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "hello world");
    vm.pop();
    vm.clear_pending_host_func();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 5);
}

#[test]
fn basic_polymorphism() {
    let src = r#"
fn first(p: (T, T)) -> T {
    let (one, two) = p
    one
}

let one = first((1, 2))
let one = ToString.str(one)
let two = first(("one", "two"))
one .. two
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "1one");
}

#[test]
fn basic_polymorphism_alternate_syntax() {
    let src = r#"
fn first(p: (T, T)) -> T {
    let (one, two) = p
    one
}

let one = first((1, 2))
let one = ToString.str(one)
let two = first(("one", "two"))
one .. two
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "1one");
}

#[test]
fn struct_assign_and_access1() {
    let src = r#"
type person = {
    name: string
    age: int
}
let x = person("Alice", 30)
x.name = "Bob"
x.age = 2 * 3 * 6
x.name
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "Bob");
}

#[test]
fn struct_assign_and_access2() {
    let src = r#"
type person = {
    name: string
    age: int
}
let x = person("Alice", 30)
x.name = "Bob"
x.age = 2 * 3 * 6
x.age
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 36);
}

#[test]
fn array_assign_and_access() {
    let src = r#"
let arr = [ 1, 2, 3, 4 ]
arr[2]
arr[2] = 33
arr[2]
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 33);
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
first.x = 20
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 20);
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
snake.body[0].x = 20
snake.body[0].x
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 20);
}

#[test]
fn match_int() {
    let src = r#"
let n = 1
match n {
    0 -> 0,
    1 -> 1,
    _ -> 2
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 1);
}

#[test]
fn match_int_wild() {
    let src = r#"
let n = 42
match n {
    0 -> 0,
    1 -> 1,
    _ -> 99
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 99);
}

#[test]
fn match_trailing_comma() {
    let src = r#"
let n = 42
match n {
    0 -> 0,
    1 -> 1,
    _ -> 99,
}
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 99);
}

#[test]
fn match_two_bools() {
    let src = r#"
let b = true
let one = match b {
    true -> 1,
    false -> 2
}
let b = false
let two = match b {
    true -> 1,
    false -> 2
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 3);
}

#[test]
fn match_pair_first_case() {
    let src = r#"
let triplet = (1, 1)
match triplet {
      (1, 1) -> 100,
      (1, 2) -> 101,
      _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 100);
}

#[test]
fn match_pair_second_case() {
    let src = r#"
let pair = (1, 2)
match pair {
      (1, 1) -> 100,
      (1, 2) -> 101,
      _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 101);
}

#[test]
fn match_pair_wild() {
    let src = r#"
let pair = (2, 1)
match pair {
      (1, 1) -> 100,
      (1, 2) -> 101,
      _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 102);
}

#[test]
fn match_quintuple_booleans() {
    let src = r#"
let quintuple = (true, false, true, true, false)
match quintuple {
      (true, false, true, true, true) -> 100,
      (true, false, true, true, false) -> 101,
      _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 101);
}

#[test]
fn match_nested_tuple() {
    let src = r#"
let triplet = (1, (2, 3), 4)
match triplet {
      (1, (2, 88), 4) -> 100,
      (1, (2, 3), 4) -> 101,
      _ -> 102
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 101);
}

#[test]
fn pattern_tuples_binding() {
    let src = r#"
let xs = (1, (2, 3))
match xs {
      (x, (y, z)) -> y
}"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 2);
}

#[test]
fn recursive_identity_function() {
    let src = r#"
fn r(n) {
    match n {
        0 -> 0,
        _ -> 1 + r(n-1)
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 2);
}

#[test]
fn fib_naive() {
    let src = r#"
fn fib(n) {
    match n {
        0 -> 0,
        1 -> 1,
        _ -> fib(n-1) + fib(n-2)
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 55);
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 10);
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 5);
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
    let top = vm.top();
    assert_eq!(top.get_float(&vm), 2.0);
}

#[test]
fn array_push() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
arr.push(6)
arr[5]
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6);
}

#[test]
fn array_len_old() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
array_length(arr)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 5);
}

#[test]
fn array_len() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
arr.len()
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 5);
}

#[test]
fn array_pop() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
arr.pop()
arr.len()
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 4);
}

#[test]
fn not() {
    let src = r#"
let b = true
not(b)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_bool(&vm), false);
}

#[test]
fn concat_strings() {
    let src = r#"
let s = "hello " .. "world"
s
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "hello world");
}

#[test]
fn monomorphize_to_string_int() {
    let src = r#"
ToString.str(123)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "123");
}

#[test]
fn monomorphize_to_string_float() {
    let src = r#"
ToString.str(123)
ToString.str(123.456)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "123.456");
}

#[test]
fn monomorphize_to_string_tuple_ints() {
    let src = r#"
let nums = (1, 2, 3)
ToString.str(nums)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "(1, 2, 3)");
}

#[test]
fn local_in_while_scope() {
    let src = r#"
    var x = 5
    while x > 0 {
        let tmp = x
        x = tmp - 1
    }
    5
    "#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 5);
}

#[test]
fn continue_and_break() {
    let src = r#"
    var i = 0
    while true {
        if i < 10 {
            i = i + 1
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 10);
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 55);
}

#[test]
fn unwrap_good() {
    let src = r#"
let m: option<int> = option.some(3)
m!
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 3);
}

#[test]
fn unwrap_bad() {
    let src = r#"
let m: option<int> = option.none
m!
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let VmStatus::Error(_) = vm.status() else { panic!() };
}

// TODO: re-enable
#[ignore]
#[test]
fn garbage_collection_once() {
    let src = r#"
var i = 0
var x = 3
while i < 10000 {
    let p = (1, 2, 3)
    let (a, b, c) = p
    x = a + b + c
    i = i + 1
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
    // vm.gc();
    assert!(vm.nbytes() < 10000);
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6);
}

// TODO: re-enable
#[ignore]
#[test]
fn garbage_collection_repeated() {
    let src = r#"
var i = 0
var x = 3
while i < 10000 {
    let p = (1, 2, 3)
    let (a, b, c) = p
    x = a + b + c
    i = i + 1
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
        // vm.gc();
        assert!(vm.nbytes() < 10000); // TODO: this test never fails!
    }
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6);
}

// #[test]
// fn entry_point() {
//     let src = r#"
// fn my_entry_point() {
//     print_string("hello world")
// }
//
// my_entry_point()
// my_entry_point()
//
// 5
// "#;
//     let program = unwrap_or_panic(compile_bytecode(
//         "main.abra",
//         MockFileProvider::single_file(src),
//     ));
//     let mut vm = Vm::with_entry_point(program, "main.my_entry_point".to_owned());
//     vm.run();
//     let top = vm.top();
//     assert_eq!(top.view_string(&vm), "hello world");
//     vm.pop();
//     vm.push_nil();
//     vm.clear_pending_host_func();
//     vm.run();
// }
//
// #[test]
// fn entry_point_with_args() {
//     let src = r#"
// fn my_entry_point(x, y) {
//     x + y
// }
//
// my_entry_point(5, 6)
// "#;
//     let program = unwrap_or_panic(compile_bytecode(
//         "main.abra",
//         MockFileProvider::single_file(src),
//     ));
//     dbg!(&program.label_map);
//     let mut vm = Vm::with_entry_point(program, "main.my_entry_point".to_owned());
//     vm.push_int(2);
//     vm.push_int(3);
//     vm.increment_stack_base(2);
//     vm.run();
//     let top = vm.top();
//     assert_eq!(top.get_int(&vm), 5);
// }

#[test]
fn import_all() {
    let util = r#"
fn foo(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util

fn bar(x: T) -> T {
  x
}

foo(2, 2)
"#;
    let mut files: HashMap<PathBuf, String> = HashMap::default();
    files.insert("main.abra".into(), main.into());
    files.insert("util.abra".into(), util.into());
    let file_provider = MockFileProvider::new(files);

    let program = compile_bytecode("main.abra", file_provider);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 4);
}

#[test]
fn import_single() {
    let util = r#"
fn foo(a: int, b) {
  a * b
}

fn bar(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util.foo

fn bar(a: int, b) {
  a + b
}

foo(6, 7)
"#;
    let mut files: HashMap<PathBuf, String> = HashMap::default();
    files.insert("main.abra".into(), main.into());
    files.insert("util.abra".into(), util.into());
    let file_provider = MockFileProvider::new(files);

    let program = compile_bytecode("main.abra", file_provider);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 42);
}

#[test]
fn import_except() {
    let util = r#"
fn foo(a: int, b) {
  a * b
}

fn bar(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util except bar

fn bar(a: int, b) {
  a + b
}

foo(6, 7)
"#;
    let mut files: HashMap<PathBuf, String> = HashMap::default();
    files.insert("main.abra".into(), main.into());
    files.insert("util.abra".into(), util.into());
    let file_provider = MockFileProvider::new(files);

    let program = compile_bytecode("main.abra", file_provider);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 42);
}

#[test]
fn import_single_plural() {
    let util = r#"
fn foo(a: int, b) {
  a * b
}

fn foo2(a: int, b) {
  a * b
}

fn bar(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util.(foo, foo2)

fn bar(a: int, b) {
  a + b
}

foo(6, 7) + foo2(6, 7)
"#;
    let mut files: HashMap<PathBuf, String> = HashMap::default();
    files.insert("main.abra".into(), main.into());
    files.insert("util.abra".into(), util.into());
    let file_provider = MockFileProvider::new(files);

    let program = compile_bytecode("main.abra", file_provider);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 84);
}

#[test]
fn import_except_plural() {
    let util = r#"
fn foo(a: int, b) {
  a * b
}

fn bar(a: int, b) {
  a + b
}

fn bar2(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util except (bar, bar2)

fn bar(a: int, b) {
  a + b
}

fn bar2(a: int, b) {
  a + b
}

foo(6, 7)
"#;
    let mut files: HashMap<PathBuf, String> = HashMap::default();
    files.insert("main.abra".into(), main.into());
    files.insert("util.abra".into(), util.into());
    let file_provider = MockFileProvider::new(files);

    let program = compile_bytecode("main.abra", file_provider);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 42);
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
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "123truefalse");
}

#[test]
fn ampersand() {
    let src = r#"
123 .. true .. false
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "123truefalse");
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
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 4);
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
    let VmStatus::PendingHostFunc(0) = status else { panic!() };
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
    let VmStatus::PendingHostFunc(1) = status else { panic!() };
    vm.push_int(3);
    vm.clear_pending_host_func();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6);
}

#[test]
fn member_functions() {
    let src = r#"
type Person = {
	first_name: string
	last_name: string
	age: int
}

type Color =
| Red
| Blue
| Green

extend Person {
	fn fullname(self) -> string {
		self.first_name .. " " .. self.last_name
	}
}

extend Color {
  fn shout(self) -> string {
    match self {
      .Red -> "red!",
      _ -> "not red!",
    }
  }
}

let p: Person = Person("Anand", "Dukkipati", 26)
let c: Color = Color.Red
p.fullname() .. " " .. c.shout()

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "Anand Dukkipati red!");
}

#[test]
fn member_functions_same_name() {
    let src = r#"
type Person = {
	first_name: string
	last_name: string
	age: int
}

type Color =
| Red
| Blue
| Green

extend Person {
	fn fullname(self) -> string {
		self.first_name .. " " .. self.last_name
	}
}

extend Color {
  fn fullname(self) -> string {
    match self {
      .Red -> "red!",
      _ -> "not red!",
    }
  }
}

let p: Person = Person("Anand", "Dukkipati", 26)
let c: Color = Color.Red
p.fullname() .. " " .. c.fullname()

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "Anand Dukkipati red!");
}

#[test]
fn member_function_fully_qualified() {
    let src = r#"
type Person = {
	first_name: string
	last_name: string
	age: int
}

extend Person {
	fn fullname(self) -> string {
		self.first_name .. " " .. self.last_name
	}
}

type Color =
| Red
| Blue
| Green

extend Color {
  fn shout(self) -> string {
    match self {
      .Red -> "red!",
      _ -> "not red!",
    }
  }
}

let p: Person = Person("Anand", "Dukkipati", 26)
Person.fullname(p) .. " " .. Color.shout(Color.Red)

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "Anand Dukkipati red!");
}

#[test]
fn interface_method_fully_qualified() {
    let src = r#"
let blah = 12345
ToString.str(blah)
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "12345");
}

#[test]
fn interface_method_dot_syntax() {
    let src = r#"
let blah = 12345
blah.str()
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "12345");
}

#[test]
fn clone_array() {
    let src = r#"
let blah = [1, 2, 3, 4, 5]
let blerp = blah.clone()

blerp.pop()
blerp.pop()

blah.len()
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 5);
}

#[test]
fn equality_struct() {
    let src = r#"
// types
type Point = {
  x: int
  y: int
}

implement Equal for Point {
  fn equal(p1: Point, p2: Point) {
    (p1.x == p2.x) and (p1.y == p2.y)
  }
}

let p1 = Point(2, 3)
let p2 = Point(2, 3)
p1 == p2

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert!(top.get_bool(&vm))
}

#[test]
fn iterate() {
    let src = r#"
let arr = [1, 2, 3]
var sum = 0
let it = arr.make_iterator()
while true {
  match it.next() {
    option.some(n) -> sum = sum + n,
    option.none -> break,
  }
}

sum

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6)
}

#[test]
fn for_loop() {
    let src = r#"
let arr = [1, 2, 3]
var sum = 0

for n in arr {
    sum = sum + n
}
sum

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6)
}

#[test]
fn range() {
    let src = r#"
var sum = 0

for n in range(4) {
    sum = sum + n
}
sum

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 6)
}

#[test]
fn struct_with_void_field() {
    let src = r#"
type person = {
    name: string
    blah: void
    age: int
}
let x = person("Alice", (), 30)
x.name = "Bob"
x.age = 2 * 3 * 6
x.name ..  " " .. x.age
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "Bob 36");
}

#[test]
fn tuple_with_void_field() {
    let src = r#"
let person = ("Alice", (), 30)
let (name, blah, age) = person
name ..  " " .. age
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.view_string(&vm), "Alice 30");
}

#[test]
fn match_tuple_with_void_field() {
    let src = r#"
let person = ("Alice", (), (), (), (), 30)
let n = match person {
  ("Bob", (), (), (), (), 50) -> 0,
  ("Alice", (), (), (), (), 20) -> 0,
  ("Alice", (), (), (), (), 30) -> 1
}
n
"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 1);
}

#[test]
fn enum_with_void_field() {
    let src = r#"
type GlibbyGlob =
| Glob(int, void, int)
| Glib

let glib = GlibbyGlob.Glib
let glob = GlibbyGlob.Glob(2, (), 5)
var n = match glob {
  GlibbyGlob.Glob(a, blah, c) -> a + c,
  GlibbyGlob.Glib -> 0
}
n = n + match glib {
  GlibbyGlob.Glob(a, blah, c) -> 0,
  GlibbyGlob.Glib -> 3,
}

n

"#;
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(&vm), 10);
}
