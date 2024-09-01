use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
    test();
    println!("PASSED");
}

fn test() {
    let src = r#"
var x = 3
if true {
    x <- x + x
}
x
"#;
    let sources = source_files_single(src);
    // TODO this should return a Vm and not leak details about string table etc.
    let vm = compile_bytecode::<DefaultEffects>(sources);
    if let Err(e) = vm {
        panic!("{}", e);
    }
    let mut vm = vm.unwrap();
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}
