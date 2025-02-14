use abra_core::effects::{DefaultEffects, EffectTrait};
use abra_core::prelude::PRELUDE;
use abra_core::vm::Vm;
use abra_core::FileData;
use abra_core::{compile_bytecode, FileProviderDefault};

fn main() {
    test();
    println!("PASSED");
}

fn test() {
    let util = r#"
fn foo(a: int, b) {
  a + b
}
"#;
    let main = r#"
use util

fn bar(x: 'a) -> 'a {
  x
}

foo(2, 2)
"#;
    let sources = vec![
        FileData::new(
            "prelude.abra".to_owned(),
            "prelude.abra".into(), // TODO: does Path actually make sense in this context?
            PRELUDE.to_owned(),
        ),
        FileData::new("util.abra".to_owned(), "util.abra".into(), util.to_owned()),
        FileData::new("main.abra".to_owned(), "main.abra".into(), main.to_owned()),
    ];
    let effects = DefaultEffects::enumerate();
    let program = compile_bytecode(sources, effects, FileProviderDefault::new());
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 4);
    println!("result is {}", top.get_int());
}
