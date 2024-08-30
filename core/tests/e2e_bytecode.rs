use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

#[test]
fn arithmetic() {
    let src = r#"
func subtract(x, y) {
  x - y
}
let x = 3
let y = 4
let z = subtract(x, y)
let h = subtract(z, 1)
h
"#;
    let sources = source_files_single(src);
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), -2);
    println!("result is {}", top.get_int());
}

#[test]
fn tuples() {
    let src = r#"
func mk_pair(a) {
  (a, a)
}
let n = 3
let p = mk_pair(n)
let (x, y) = p
x + y
"#;
    let sources = source_files_single(src);
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
    println!("result is {}", top.get_int());
}

#[test]
fn just_if() {
    let src = r#"
let mutable x = 3
if true {
    x <- x + x
}
x
"#;
    let sources = source_files_single(src);
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 2);
}

#[test]
fn recursive_identity_function() {
    let src = r#"
func r(n) {
    match n {
        0 -> 0
        _ -> 1 + r(n-1)
    }
}
r(2)
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 2);
}

#[test]
fn fib_naive() {
    let src = r#"
func fib(n) {
    match n {
        0 -> 0
        1 -> 1
        _ -> fib(n-1) + fib(n-2)
    }
}
fib(10)
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 55);
}

fn lambda_no_capture() {
    let src = r#"
let double = x -> x + x
double(5)
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 3);
}

#[test]
fn sqrt_float() {
    let src = r#"
let f = 4.0
let g = sqrt(f)
g
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
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
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 1);
}

#[test]
fn list_literal_total() {
    let src = r#"
let xs = [| 1, 2, 3 |]

func total(xs) {
    match xs {
      cons(~x, ~xs) -> x + total(xs)
      nil -> 0
    }
}

total(xs)
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}

#[test]
fn parametric_polymorphic_func() {
    let src = r#"
let nums = [| 1, 2, 3 |]
let bools = [| true, false, true, true, false |]

func list_len(xs) {
    match xs {
      cons(_, ~xs) -> 1 + list_len(xs)
      nil -> 0
    }
}

list_len(nums) + list_len(bools)
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 8);
}
