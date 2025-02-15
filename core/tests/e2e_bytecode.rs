use abra_core::compile_bytecode;
use abra_core::effects::DefaultEffects;
use abra_core::effects::EffectTrait;
use abra_core::prelude::PRELUDE;
use abra_core::source_files_single;
use abra_core::vm::Vm;

pub mod utils;
use abra_core::FileData;
use abra_core::FileProviderDefault;
use utils::inner::unwrap_or_panic;

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
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), -2);
    println!("result is {}", top.get_int());
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
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
    println!("result is {}", top.get_int());
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
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
    println!("result is {}", top.get_int());
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
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
    println!("result is {}", top.get_int());
}

#[test]
fn print_string() {
    let src = r#"
print_string("hello world")
5
"#;
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "hello world");
    vm.pop();
    vm.push_nil();
    vm.clear_pending_effect();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
}

#[test]
fn struct_assign_and_access1() {
    let src = r#"
type person = {
    name: string,
    age: int
}
let x = person("Alice", 30)
x.name <- "Bob"
x.age <- 2 * 3 * 6
x.name
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "Bob");
}

#[test]
fn struct_assign_and_access2() {
    let src = r#"
type person = {
    name: string,
    age: int
}
let x = person("Alice", 30)
x.name <- "Bob"
x.age <- 2 * 3 * 6
x.age
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 36);
}

#[test]
fn array_assign_and_access() {
    let src = r#"
let arr = [ 1, 2, 3, 4 ]
arr[2]
arr[2] <- 33
arr[2]
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 33);
}

#[test]
fn match_int() {
    let src = r#"
let n = 1
match n {
  0 -> 0
  1 -> 1
  _ -> 2
}
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 1);
}

#[test]
fn match_int_wild() {
    let src = r#"
let n = 42
match n {
  0 -> 0
  1 -> 1
  _ -> 99
}
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 99);
}

#[test]
fn match_two_bools() {
    let src = r#"
let b = true
let one = match b {
  true -> 1
  false -> 2
}
let b = false
let two = match b {
  true -> 1
  false -> 2
}
let sum = one + two
sum
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 3);
}

#[test]
fn match_pair_first_case() {
    let src = r#"
let triplet = (1, 1)
match triplet {
    (1, 1) -> 100
    (1, 2) -> 101
    _ -> 102
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 100);
}

#[test]
fn match_pair_second_case() {
    let src = r#"
let pair = (1, 2)
match pair {
    (1, 1) -> 100
    (1, 2) -> 101
    _ -> 102
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 101);
}

#[test]
fn match_pair_wild() {
    let src = r#"
let pair = (2, 1)
match pair {
    (1, 1) -> 100
    (1, 2) -> 101
    _ -> 102
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 102);
}

#[test]
fn match_quintuple_booleans() {
    let src = r#"
let quintuple = (true, false, true, true, false)
match quintuple {
    (true, false, true, true, true) -> 100
    (true, false, true, true, false) -> 101
    _ -> 102
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 101);
}

#[test]
fn match_nested_tuple() {
    let src = r#"
let triplet = (1, (2, 3), 4)
match triplet {
    (1, (2, 88), 4) -> 100
    (1, (2, 3), 4) -> 101
    _ -> 102
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 101);
}

#[test]
fn pattern_tuples_binding() {
    let src = r#"
let xs = (1, (2, 3))
match xs {
    (~x, (~y, ~z)) -> y
}"#;
    //     let src = r#"
    // let xs = nil
    // match xs {
    //     cons(~x, _) -> 9
    //     nil -> 100
    // }"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 2);
}

#[test]
fn match_cons_binding() {
    let src = r#"
let xs = cons(23, nil)
match xs {
    nil -> 100
    cons(~x, _) -> x
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 23);
}

#[test]
fn match_cons_binding_nested() {
    let src = r#"
let xs = cons(1, cons(2, nil))
match xs {
    nil -> 100
    cons(_, cons(~x, nil)) -> x
    _ -> 101
}"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 2);
}

#[test]
fn recursive_identity_function() {
    let src = r#"
fn r(n) {
    match n {
        0 -> 0
        _ -> 1 + r(n-1)
    }
}
r(2)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 2);
}

#[test]
fn fib_naive() {
    let src = r#"
fn fib(n) {
    match n {
        0 -> 0
        1 -> 1
        _ -> fib(n-1) + fib(n-2)
    }
}
fib(10)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 55);
}

#[test]
fn lambda_no_capture() {
    let src = r#"
let double = x -> x + x
double(5)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 10);
}

#[test]
fn lambda_no_capture_2_args() {
    let src = r#"
let add = (x, y) -> x + y
add(2, 3)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
}

#[test]
fn lambda_capture() {
    let src = r#"
let one = 1
let add1 = x -> x + one
add1(4)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
}

#[test]
fn lambda_capture2() {
    let src = r#"
let one = 1
let two = 2
let sub1 = x -> x + one - two
sub1(4)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 3);
}

#[test]
fn sqrt_float() {
    let src = r#"
let f = 4.0
let g = sqrt_float(f)
g
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_float(), 2.0);
}

#[test]
fn array_append() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
append(arr, 6)
arr[5]
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}

#[test]
fn array_len() {
    let src = r#"
let arr = [1, 2, 3, 4, 5]
len(arr)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
}

#[test]
fn list_literal_head() {
    let src = r#"
match [| 1, 2, 3 |] {
  nil -> 0
  cons(~x, _) -> x
}
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 1);
}

#[test]
fn list_literal_total() {
    let src = r#"
let xs = [| 1, 2, 3 |]

fn total(xs) {
    match xs {
      cons(~x, ~xs) -> x + total(xs)
      nil -> 0
    }
}

total(xs)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}

#[test]
fn parametric_polymorphic_func() {
    let src = r#"
let nums = [| 1, 2, 3 |]
let bools = [| true, false, true, true, false |]

fn list_len(xs: list<'a>) {
    match xs {
      cons(_, ~xs) -> 1 + list_len(xs)
      nil -> 0
    }
}

list_len(nums) + list_len(bools)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 8);
}

#[test]
fn concat_strings() {
    let src = r#"
let s = "hello " & "world"
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "hello world");
}

#[test]
fn monomorphize_to_string_int() {
    let src = r#"
str(123)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "123");
}

#[test]
fn monomorphize_to_string_float() {
    let src = r#"
str(123)
str(123.456)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "123.456");
}

#[test]
fn monomorphize_to_string_tuple_ints() {
    let src = r#"
let nums = (1, 2, 3)
str(nums)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "(1, 2, 3)");
}

#[test]
fn monomorphize_overloaded_func_println() {
    let src = r#"
str(123)
println(123)
5
"#;
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "123\n");
    vm.pop();
    vm.push_nil();
    vm.clear_pending_effect();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
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
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
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
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 10);
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
    let sources = source_files_single(src);

    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 55);
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
    let sources = source_files_single(src);

    let vm = compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    );
    if let Err(e) = vm {
        panic!("{}", e);
    }
    let program = vm.unwrap();
    let mut vm = Vm::new(program);
    while !vm.is_done() {
        vm.run_n_steps(1);
    }
    vm.gc();
    assert!(vm.nbytes() < 10000);
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
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
    let sources = source_files_single(src);

    let vm = compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    );
    if let Err(e) = vm {
        panic!("{}", e);
    }
    let program = vm.unwrap();
    let mut vm = Vm::new(program);
    while !vm.is_done() {
        vm.run_n_steps(1);
        vm.gc();
        assert!(vm.nbytes() < 10000);
    }
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}

#[test]
fn entry_point() {
    let src = r#"
fn main() {
    print_string("hello world")
}

5
"#;
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::with_entry_point(program, "test.main".to_owned());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "hello world");
    vm.pop();
    vm.push_nil();
    vm.clear_pending_effect();
    vm.run();
}

#[test]
fn entry_point_with_args() {
    let src = r#"
fn main(x, y) {
    x + y
}

main(5, 6)
"#;
    let sources = source_files_single(src);
    let program = unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ));
    let mut vm = Vm::with_entry_point(program, "test.main".to_owned());
    vm.push_int(2);
    vm.push_int(3);
    vm.increment_stack_base(2);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
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
    let sources = vec![
        FileData::new("main.abra".into(), main.to_owned()),
        FileData::new("util.abra".into(), util.to_owned()),
        FileData::new("prelude.abra".into(), PRELUDE.to_owned()),
    ];
    let effects = DefaultEffects::enumerate();
    let program = compile_bytecode(sources, effects, FileProviderDefault::new());
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
    println!("result is {}", top.get_int());
}

#[test]
fn format_append() {
    let src = r#"
format_append(format_append(123, true), false)
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "123truefalse");
}

#[test]
fn ampersand() {
    let src = r#"
123 & true & false
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "123truefalse");
}

#[test]
fn comments() {
    let src = r#"
// single-line comment
2 + 2 // => 4
/* multi-line
comment */
"#;
    let sources = source_files_single(src);
    let program = match compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::new(),
    ) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
}
