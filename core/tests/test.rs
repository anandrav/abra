use abra_core::*;

#[test]
fn basic() {
    let contents = "2+2".to_owned();
    let source_file = SourceFile {
        name: "main.abra".to_owned(),
        contents,
    };
    let prelude = SourceFile {
        name: "prelude.abra".to_owned(),
        contents: _PRELUDE.to_string(),
    };
    let source_files = vec![prelude, source_file];
    let runtime = compile::<side_effects::Effect>(source_files);
    let runtime = runtime.unwrap();
    let mut interpreter = runtime.toplevel_interpreter();
    let mut effect_result = None;
    while !interpreter.is_finished() {
        interpreter.run(10000, effect_result.take());
    }
    assert_eq!(interpreter.get_val().unwrap(), runtime.make_int(4));
}
