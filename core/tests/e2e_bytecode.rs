use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;
use abra_core::vm::Vm;

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
    let bytecode = compile_bytecode::<DefaultEffects>(sources).unwrap();

    let mut vm = Vm::new(bytecode);
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
    let bytecode = compile_bytecode::<DefaultEffects>(sources).unwrap();

    let mut vm = Vm::new(bytecode);
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
    let bytecode = compile_bytecode::<DefaultEffects>(sources).unwrap();

    let mut vm = Vm::new(bytecode);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
    println!("result is {}", top.get_int());
}
