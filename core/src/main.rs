use abra_core::effects::{DefaultEffects, EffectTrait};
use abra_core::vm::Vm;
use abra_core::SourceFile;
use abra_core::{compile_bytecode, _PRELUDE};

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
            contents: _PRELUDE.to_owned(),
        },
        SourceFile {
            name: "util.abra".to_owned(),
            contents: util.to_owned(),
        },
        SourceFile {
            name: "main.abra".to_owned(),
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
