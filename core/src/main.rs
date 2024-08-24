use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
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
