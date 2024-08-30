use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
    let src = r#"
let s = "hello " & "world"
"#;
    let sources = source_files_single(src);
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_string(&vm), "hello world");
}
