use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;
use abra_core::vm::Vm;

fn main() {
    test();
    println!("PASSED");
}

fn test() {
    let src = r#"

func my_api() {
    1
}

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
    let program = compile_bytecode::<DefaultEffects>(sources);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    while !vm.is_done() {
        vm.run_n_steps(1);
        vm.gc();
        assert!(vm.nbytes() < 10000);
    }
    let top = vm.top();
    assert_eq!(top.get_int(), 6);
}
