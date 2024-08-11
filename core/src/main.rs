use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;
use abra_core::vm::Vm;

fn main() {
    let src = r#"
println("hello world")
"#;
    let sources = source_files_single(src);
    // TODO this should return a Vm and not leak details about string table etc.
    let bytecode = compile_bytecode::<DefaultEffects>(sources).unwrap();

    let mut vm = Vm::new(bytecode);
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
    println!("result is {}", top.get_int());
}
