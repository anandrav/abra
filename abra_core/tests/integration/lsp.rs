/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::{MockFileProvider, check_lsp};

fn analyze(src: &str) -> abra_core::AnalysisResult {
    check_lsp("main.abra", MockFileProvider::single_file(src))
}

fn offset_of(src: &str, needle: &str) -> usize {
    src.find(needle)
        .unwrap_or_else(|| panic!("needle not found: {needle:?}"))
}

fn nth_offset_of(src: &str, needle: &str, n: usize) -> usize {
    let mut start = 0;
    for _ in 0..n {
        let i = src[start..]
            .find(needle)
            .unwrap_or_else(|| panic!("only found < {n} occurrences of {needle:?}"));
        start += i + needle.len();
    }
    let i = src[start..]
        .find(needle)
        .unwrap_or_else(|| panic!("only found {n} occurrences of {needle:?}"));
    start + i
}

#[track_caller]
fn assert_def_at(src: &str, query_offset: usize, expected_def: &str) {
    let analysis = analyze(src);
    let def = analysis
        .definition_at(0, query_offset)
        .unwrap_or_else(|| panic!("no definition found at offset {query_offset}"));
    let actual = &src[def.range.clone()];
    assert_eq!(
        actual, expected_def,
        "expected definition `{expected_def}` got `{actual}`"
    );
}

// Fix #1: MemberAccessLeadingDot should resolve to its enum variant.
#[test]
fn def_unqualified_variant_in_let() {
    let src = "type Color = Red | Green | Blue\nlet c: Color = .Red\n";
    let q = offset_of(src, ".Red") + 1; // position on 'R' of `.Red`
    assert_def_at(src, q, "Red");
}

#[test]
fn def_unqualified_variant_in_call() {
    let src = "type Tree<T> = Leaf | Node(T)\nlet t: Tree<int> = .Node(3)\n";
    let q = offset_of(src, ".Node") + 1;
    // Variant loc covers the constructor and its data type
    assert_def_at(src, q, "Node(T)");
}

// Fix #2: pattern variant tags should be reachable for go-to-def.
#[test]
fn def_pattern_variant_tag_in_match() {
    let src = "\
type Color = Red | Green
fn pick(c: Color) -> int {
    match c {
        .Red -> 1
        .Green -> 2
    }
}
let x = pick(.Red)
";
    // .Red inside the match arm
    let arm_red = nth_offset_of(src, ".Red", 0) + 1;
    assert_def_at(src, arm_red, "Red");
    // .Green inside the match arm
    let arm_green = offset_of(src, ".Green") + 1;
    assert_def_at(src, arm_green, "Green");
}

#[test]
fn def_pattern_variant_tag_with_data() {
    let src = "\
type Box = Empty | Full(int)
fn unwrap(b: Box) -> int {
    match b {
        .Full(n) -> n
        .Empty -> 0
    }
}
";
    // .Full inside the match arm
    let arm_full = offset_of(src, ".Full(n)") + 1;
    assert_def_at(src, arm_full, "Full(int)");
}

// Fix #3: identifiers inside type and interface definitions should be reachable.
#[test]
fn def_struct_field_named_type() {
    let src = "\
type Color = Red | Green
type Pixel = { color: Color, brightness: int }
";
    let q = offset_of(src, "color: Color") + "color: ".len();
    assert_def_at(src, q, "Color");
}

#[test]
fn def_enum_variant_data_type() {
    let src = "\
type Wrapper = { val: int }
type Box = Empty | Full(Wrapper)
";
    let q = offset_of(src, "Full(Wrapper)") + "Full(".len();
    assert_def_at(src, q, "Wrapper");
}

#[test]
fn def_struct_polytype_arg_used_in_field() {
    let src = "type Container<T> = { item: T }\n";
    // T in `item: T` should resolve to T in `Container<T>`
    let q = offset_of(src, "item: T") + "item: ".len();
    assert_def_at(src, q, "T");
}

#[test]
fn def_interface_method_arg_type() {
    let src = "\
type Color = Red | Green
interface Painter {
    fn paint(self: Self, c: Color) -> int
}
";
    let q = offset_of(src, "c: Color") + "c: ".len();
    assert_def_at(src, q, "Color");
}

// Fix #4: interface constraint names on type parameters should be reachable.
#[test]
fn def_polytype_interface_constraint() {
    let src = "\
interface Doubleable {
    fn doubl(self: Self) -> Self
}
fn twice(x: T Doubleable) -> T = x.doubl()
";
    let q = offset_of(src, "T Doubleable") + "T ".len();
    assert_def_at(src, q, "Doubleable");
}

// Fix #5: named arguments in function calls should be reachable.
#[test]
fn def_named_argument() {
    let src = "\
fn greet(name: string, greeting: string = \"hi\") -> string = greeting .. name
let _ = greet(name = \"Alice\")
";
    let q = offset_of(src, "name = \"Alice\"");
    assert_def_at(src, q, "name");
}

// Fix #6: lambda signatures should be reachable for go-to-def.
#[test]
fn def_lambda_arg_type_annotation() {
    let src = "\
type Color = Red | Green
let f = (c: Color) -> 1
";
    let q = offset_of(src, "(c: Color)") + "(c: ".len();
    assert_def_at(src, q, "Color");
}
