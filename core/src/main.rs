use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;
use abra_core::vm::Vm;

fn main() {
    let src = r#"
let x = 3
let y = 4
x + y
"#;
    let sources = source_files_single(src);
    let bytecode = compile_bytecode::<DefaultEffects>(sources).unwrap();

    let mut vm = Vm::new(bytecode);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 7);
    println!("result is {}", top.get_int());
}
