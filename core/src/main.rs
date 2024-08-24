use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
    let src = r#"
type person = {
    name: string,
    age: int
}
let user = person("Alice", 30)
user.name <- "Bob"
user.name
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
