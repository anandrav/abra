use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
    test();
    println!("PASSED");
}

fn test() {
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
    // TODO this should return a Vm and not leak details about string table etc.
    let vm = compile_bytecode::<DefaultEffects>(sources);
    if let Err(e) = vm {
        panic!("{}", e);
    }
    let mut vm = vm.unwrap();
    while !vm.is_done() {
        vm.run_n_steps(1);
        vm.gc();
        println!("heap size: {}", vm.heap_size());
        println!("nbytes size: {}", vm.nbytes());
    }
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}
