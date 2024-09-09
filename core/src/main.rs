use abra_core::compile_bytecode;
use abra_core::effects::{DefaultEffects, EffectTrait};
use abra_core::source_files_single;
use abra_core::vm::Vm;

fn main() {
    test();
    println!("PASSED");
}

fn test() {
    let src = r#"
if false {
  3
} else {
  4
}
"#;
    let sources = source_files_single(src);
    let effects = DefaultEffects::enumerate();
    let program = compile_bytecode(sources, effects);
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
    println!("result is {}", top.get_int());
}
