/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::helper::unwrap_or_panic;
use abra_core::MockFileProvider;
use abra_core::compile_bytecode;

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
    unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
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
    unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
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
    unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
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
    unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
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
    unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
}

// NEGATIVE TESTS
// Typechecking should catch an error.

fn should_fail(src: &str) {
    compile_bytecode("main.abra", MockFileProvider::single_file(src)).unwrap_err();
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
