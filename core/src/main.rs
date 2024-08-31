use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
    let src = r#"
to_string(123)
println(123)
5
"#;
    let sources = source_files_single(src);
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = compile_bytecode::<DefaultEffects>(sources).unwrap();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "123");
    vm.pop();
    vm.push_nil();
    vm.clear_pending_effect();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "\n");
    vm.pop();
    vm.push_nil();
    vm.clear_pending_effect();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 5);
}
