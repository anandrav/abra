use abra_core::compile_bytecode;
use abra_core::effects::DefaultEffects;
use abra_core::effects::EffectTrait;
use abra_core::source_files_single;

use crate::utils::unwrap_or_panic;
use abra_core::FileProviderDefault;

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
    unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    ));
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
    unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    ));
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
    unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    ));
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
    unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    ));
}

#[test]
fn struct_fields() {
    let src = r#"
type person = {
    age: int
    name: string
}

let p = person(33, "Anand")
p.age
"#;
    let sources = source_files_single(src);
    unwrap_or_panic(compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    ));
}

// NEGATIVE TESTS
// Typechecking should catch an error.

fn should_fail(src: &str) {
    let sources = source_files_single(src);
    compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    )
    .unwrap_err();
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

#[test]
fn bad_struct_fields() {
    should_fail(
        r#"
type person = {
    name: string
    age: int
}

let p = person("25", "Anand")
"#,
    );
}

#[test]
fn bad_struct_fields2() {
    should_fail(
        r#"
type person = {
    name: string
    age: int
}

let p = person(25, "Anand")
p.age <- "25"
"#,
    );
}

#[test]
fn struct_access_type_infer() {
    should_fail(
        r#"
type person = {
    name: string
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
