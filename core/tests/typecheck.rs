use abra_core::compile_bytecode;
use abra_core::effects::DefaultEffects;
use abra_core::effects::EffectTrait;
use abra_core::source_files_single;

mod utils;
use utils::inner::unwrap_or_panic;

// POSITIVE TESTS
// Typechecking should succeed.

#[test]
fn integer_operators() {
    let src = r#"
let a = 2 + 2
let b = a * 3
let c = b / 2
let d = c - 1
let e = d ^ 2
let f = e mod 3
"#;
    let sources = source_files_single(src);
    unwrap_or_panic(compile_bytecode(sources, DefaultEffects::enumerate()));
}

#[test]
fn float_operators() {
    let src = r#"
let a = 2.0 + 2.0
let b = a * 3.0
let c = b / 2.0
let d = c - 1.0
let e = d ^ 2.0
"#;
    let sources = source_files_single(src);
    unwrap_or_panic(compile_bytecode(sources, DefaultEffects::enumerate()));
}

#[test]
fn boolean_operators() {
    let src = r#"
let x = true
let y = false
let z = x and y
let w = x or y
"#;
    let sources = source_files_single(src);
    unwrap_or_panic(compile_bytecode(sources, DefaultEffects::enumerate()));
}

#[test]
fn comparison_operators() {
    let src = r#"
let a = 2 < 3
let b = 2 <= 3
let c = 2 > 3
let d = 2 >= 3
let e = 2 = 3

let f = 2.0 < 3.0
let g = 2.0 <= 3.0
let h = 2.0 > 3.0
let i = 2.0 >= 3.0
let j = 2.0 = 3.0

let k = a and b and c and d and e and f and g and h and i and j
"#;
    let sources = source_files_single(src);
    unwrap_or_panic(compile_bytecode(sources, DefaultEffects::enumerate()));
}

// NEGATIVE TESTS
// Typechecking should catch an error.

fn should_fail(src: &str) {
    let sources = source_files_single(src);
    compile_bytecode(sources, DefaultEffects::enumerate()).unwrap_err();
}

#[test]
fn bad_add() {
    should_fail("2 + true");
}

#[test]
fn bad_add2() {
    should_fail("2.0 + 2");
}

#[test]
fn bad_comp() {
    should_fail("2 < 2.0");
}

#[test]
fn bad_comp2() {
    should_fail("true < 2");
}

// TODO: type aliases are not resolved properly
// In this case, 'person' in get_age argument annotation is not properly recognized as the 'person' type defined on first line
// TODO: consider creating a separate test file just for type checking, especially negative test cases
#[ignore]
#[test]
fn struct_access_type_infer() {
    should_fail(
        r#"
type person = {
    name: string,
    age: int
}

fn get_age(p: person) {
    p + p
}

let x = person("Alice", 30)
get_age(15)
"#,
    );
}
