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
