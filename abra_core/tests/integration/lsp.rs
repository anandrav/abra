/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::{CompletionCandidateKind, MockFileProvider, check_lsp};

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

// Fix #7: struct field access should jump to the field declaration.
#[test]
fn def_struct_field_access() {
    let src = "\
type Point = { x: int, y: int }
fn get_x(p: Point) -> int = p.x
";
    let q = offset_of(src, "p.x") + "p.".len();
    assert_def_at(src, q, "x");
}

#[test]
fn def_struct_field_access_multi_field() {
    let src = "\
type Point = {
    x: int
    y: int
}
fn get_y(p: Point) -> int = p.y
";
    let q = offset_of(src, "p.y") + "p.".len();
    assert_def_at(src, q, "y");
}

#[test]
fn def_struct_field_access_chained() {
    let src = "\
type Inner = { val: int }
type Outer = { inner: Inner }
fn get_val(o: Outer) -> int = o.inner.val
";
    // jump on `inner`
    let q1 = offset_of(src, "o.inner.val") + "o.".len();
    assert_def_at(src, q1, "inner");
    // jump on `val`
    let q2 = offset_of(src, "o.inner.val") + "o.inner.".len();
    assert_def_at(src, q2, "val");
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

// --- Completions ---

#[track_caller]
fn assert_completion_labels(src: &str, after_dot_offset: usize, expected_labels: &[&str]) {
    let analysis = analyze(src);
    let candidates = analysis.completions_at(0, after_dot_offset);
    let labels: Vec<String> = candidates.into_iter().map(|c| c.label).collect();
    for expected in expected_labels {
        assert!(
            labels.iter().any(|l| l == expected),
            "expected label {expected:?} in {labels:?}"
        );
    }
}

#[track_caller]
fn assert_has_completion(
    src: &str,
    after_dot_offset: usize,
    label: &str,
    kind: CompletionCandidateKind,
) {
    let analysis = analyze(src);
    let candidates = analysis.completions_at(0, after_dot_offset);
    let found = candidates
        .iter()
        .find(|c| c.label == label)
        .unwrap_or_else(|| panic!("missing label {label:?} in {candidates:#?}"));
    assert!(
        std::mem::discriminant(&found.kind) == std::mem::discriminant(&kind),
        "label {label:?} had kind {:?}, expected {:?}",
        found.kind,
        kind
    );
}

// Fix #11: enum used as namespace should produce variant + member function
// completions. We use a real parseable shape `Color.X` and probe the offset
// right after the dot (mid-expression).
#[test]
fn completion_enum_namespace() {
    let src = "\
type Color = Red | Green | Blue
let c = Color.Red
";
    let dot_after = offset_of(src, "Color.Red") + "Color.".len();
    assert_completion_labels(src, dot_after, &["Red", "Green", "Blue"]);
    assert_has_completion(src, dot_after, "Red", CompletionCandidateKind::EnumVariant);
}

// Fix #11: interface used as namespace should produce method completions.
#[test]
fn completion_interface_namespace() {
    let src = "\
interface Speaker {
    fn say(self: Self) -> string
    fn shout(self: Self) -> string
}
type Robot = { id: int }
implement Speaker for Robot {
    fn say(self) -> string = \"beep\"
    fn shout(self) -> string = \"BEEP\"
}
let r = Robot(1)
let s = Speaker.say(r)
";
    let dot_after = offset_of(src, "Speaker.say(r)") + "Speaker.".len();
    assert_completion_labels(src, dot_after, &["say", "shout"]);
    assert_has_completion(src, dot_after, "say", CompletionCandidateKind::Function);
}

// Fix #11: struct used as namespace yields its member functions (extension methods).
#[test]
fn completion_struct_namespace_member_fn() {
    let src = "\
type Point = { x: int }
extend Point {
    fn double(self: Point) -> int = self.x * 2
}
let p = Point(1)
let _d = Point.double(p)
";
    let dot_after = offset_of(src, "Point.double") + "Point.".len();
    assert_completion_labels(src, dot_after, &["double"]);
}

// Fix #12: completions on a let-binding work mid-expression (`p.x`) even when
// the binding is the only place the name appears.
#[test]
fn completion_struct_value_via_let_binding() {
    let src = "\
type Point = { x: int }
fn use_it() {
    let p = Point(1)
    let _q = p.x
}
";
    let dot_after = offset_of(src, "p.x") + "p.".len();
    assert_completion_labels(src, dot_after, &["x"]);
}

// Fix #12: completion via a function arg binding name with a parseable use.
#[test]
fn completion_fn_arg_binding() {
    let src = "\
type Point = { x: int }
fn use_it(p: Point) -> int = p.x
";
    let dot_after = offset_of(src, "p.x") + "p.".len();
    assert_completion_labels(src, dot_after, &["x"]);
}

// The user's diagnostic case: `Color.<TAB>` should autocomplete *just like*
// `my_struct.<TAB>` does, even when the using-item itself failed to parse
// and was dropped from the AST. The completion lookup must consult the
// file's top-level namespace, not just Variable expressions.
#[test]
fn completion_enum_namespace_only_use_dropped() {
    // The trailing dot makes this `let` line fail to parse — that item gets
    // dropped, so there is no `Variable("Color")` anywhere in the AST.
    // The only place `Color` lives is the type declaration in Item 1.
    let src = "\
type Color = Red | Green | Blue
let _t = Color.
";
    let dot_after = offset_of(src, "Color.") + "Color.".len();
    assert_completion_labels(src, dot_after, &["Red", "Green", "Blue"]);
    assert_has_completion(src, dot_after, "Red", CompletionCandidateKind::EnumVariant);
}

#[test]
fn completion_struct_namespace_only_use_dropped() {
    let src = "\
type Point = { x: int }
extend Point {
    fn double(self: Point) -> int = self.x * 2
}
let _t = Point.
";
    let dot_after = offset_of(src, "Point.\n") + "Point.".len();
    assert_completion_labels(src, dot_after, &["double"]);
}

#[test]
fn completion_interface_namespace_only_use_dropped() {
    let src = "\
interface Speaker {
    fn say(self: Self) -> string
    fn shout(self: Self) -> string
}
let _t = Speaker.
";
    let dot_after = offset_of(src, "Speaker.") + "Speaker.".len();
    assert_completion_labels(src, dot_after, &["say", "shout"]);
}
