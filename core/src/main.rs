use abra_core::compile_bytecode;
use abra_core::effects::{DefaultEffects, EffectTrait};
use abra_core::prelude::_PRELUDE;
use abra_core::vm::Vm;
use abra_core::SourceFile;

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
        SourceFile {
            name: "prelude.abra".to_owned(),
            path: "prelude.abra".into(), // TODO: does Path actually make sense in this context?
            contents: _PRELUDE.to_owned(),
        },
        SourceFile {
            name: "util.abra".to_owned(),
            path: "util.abra".into(),
            contents: util.to_owned(),
        },
        SourceFile {
            name: "main.abra".to_owned(),
            path: "main.abra".into(),
            contents: main.to_owned(),
        },
    ];
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
