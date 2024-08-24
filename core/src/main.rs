use abra_core::compile_bytecode;
use abra_core::side_effects::DefaultEffects;
use abra_core::source_files_single;

fn main() {
    let src = r#"
let triplet = (true, false, false)
match triplet {
  (true, false, false) -> 3
  _ -> 4
}"#;
    let sources = source_files_single(src);
    // TODO this should return a Vm and not leak details about string table etc.
    let mut vm = match compile_bytecode::<DefaultEffects>(sources) {
        Ok(vm) => vm,
        Err(e) => {
            panic!("{}", e);
        }
    };
    vm.run();
    let top = vm.top();
    assert_eq!(top.get_int(), 3);
}
