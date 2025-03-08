use abra_core::FileData;
use abra_core::effects::{DefaultEffects, EffectTrait};
use abra_core::prelude::PRELUDE;
use abra_core::vm::Vm;
use abra_core::{FileProviderDefault, compile_bytecode};

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
            "prelude.abra".into(),
            "prelude.abra".into(), // TODO: does Path actually make sense in this context?
            PRELUDE.to_owned(),
        ),
        FileData::new("util.abra".into(), "util.abra".into(), util.to_owned()),
        FileData::new("main.abra".into(), "main.abra".into(), main.to_owned()),
    ];
    let effects = DefaultEffects::enumerate();
    let program = compile_bytecode(
        sources,
        effects,
        FileProviderDefault::todo_get_rid_of_this(),
    );
    if let Err(e) = program {
        panic!("{}", e);
    }
    let mut vm = Vm::new(program.unwrap());
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 4);
    println!("result is {}", top.get_int(&vm).unwrap());
}
