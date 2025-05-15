/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

pub const PRELUDE: &str = r#"
host fn print_string(s: string) -> void

fn not(b: bool) = if b false else true

interface Num {
    fn add: ('a Num, 'a Num) -> 'a Num
    fn subtract: ('a Num, 'a Num) -> 'a Num
    fn multiply: ('a Num, 'a Num) -> 'a Num
    fn divide: ('a Num, 'a Num) -> 'a Num
    fn power: ('a Num, 'a Num) -> 'a Num
    fn less_than: ('a Num, 'a Num) -> bool
    fn less_than_or_equal: ('a Num, 'a Num) -> bool
    fn greater_than: ('a Num, 'a Num) -> bool
    fn greater_than_or_equal: ('a Num, 'a Num) -> bool
}

implement Num for int {
    fn add(a, b) = add_int(a, b)
    fn subtract(a, b) = subtract_int(a, b)
    fn multiply(a, b) = multiply_int(a, b)
    fn divide(a, b) = divide_int(a, b)
    fn power(a, b) = power_int(a, b)
    fn less_than(a, b) = less_than_int(a, b)
    fn less_than_or_equal(a, b) = (a < b) or (a = b)
    fn greater_than(a, b) = not(a < b) and not(a = b)
    fn greater_than_or_equal(a, b) = not(a < b)
}

implement Num for float {
    fn add(a, b) = add_float(a, b)
    fn subtract(a, b) = subtract_float(a, b)
    fn multiply(a, b) = multiply_float(a, b)
    fn divide(a, b) = divide_float(a, b)
    fn power(a, b) = power_float(a, b)
    fn less_than(a, b) = less_than_float(a, b)
    fn less_than_or_equal(a, b) = a < b
    fn greater_than(a, b) = b < a
    fn greater_than_or_equal(a, b) = b < a
}

type maybe<'y,'n> = yes of ('y) | no of ('n)

fn unwrap(m: maybe<'y,'n>) -> 'y {
    match m {
        .yes(y) -> y,
        .no(_) -> panic("could not unwrap")
    }
}

interface Equal {
    fn equal: ('a Equal, 'a Equal) -> bool
}
implement Equal for void {
    fn equal(a, b) = true
}
implement Equal for int {
    fn equal(a, b) = equal_int(a, b)
}
implement Equal for float {
    fn equal(a, b) = false
}
implement Equal for bool {
    fn equal(a, b) {
        if a and b {
            true
        } else if a or b {
            false
        } else {
            true
        }
    }
}
implement Equal for string {
    fn equal(a, b) = equal_string(a, b)
}

interface ToString {
    fn str: 'a ToString -> string
}
implement ToString for string {
	fn str(s) = s
}
implement ToString for void {
	fn str(s) = "()"
}
implement ToString for int {
	fn str(n) = int_to_string(n)
}
implement ToString for bool {
	fn str(b) = if b "true" else "false"
}
implement ToString for float {
    fn str(f) = float_to_string(f)
}
implement ToString for ('a ToString, 'b ToString) {
    fn str(p) {
        let (a, b) = p
        "(" & str(a) & ", " & str(b) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString) {
    fn str(p) {
        let (a, b, c) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString) {
    fn str(p) {
        let (a, b, c, d) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString) {
    fn str(p) {
        let (a, b, c, d, e) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString) {
    fn str(p) {
        let (a, b, c, d, e, f) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ", " & str(g) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ", " & str(g) & ", " & str(h) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ", " & str(g) & ", " & str(h) & ", " & str(i) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ", " & str(g) & ", " & str(h) & ", " & str(i) & ", " & str(j) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ", " & str(g) & ", " & str(h) & ", " & str(i) & ", " & str(j) & ", " & str(k) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString, 'l ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k, l) = p
        "(" & str(a) & ", " & str(b) & ", " & str(c) & ", " & str(d) & ", " & str(e) & ", " & str(f) & ", " & str(g) & ", " & str(h) & ", " & str(i) & ", " & str(j) & ", " & str(k) & ", " & str(l) & ")"
    }
}

implement ToString for array<'a ToString> {
    fn str(arr) {
        "[ " & array_to_string_helper(arr, 0) & " ]"
    }
}

fn array_to_string_helper(arr: array<'a ToString>, idx: int) {
    let l = array_length(arr)
    if idx = l {
        ""
    } else if idx = l - 1 {
        str(arr[idx])
    } else {
        str(arr[idx]) & ", " & array_to_string_helper(arr, idx + 1)
    }
}

fn len(arr: array<'a>) -> int { 
    array_length(arr)
}

fn append(arr: array<'a>, x: 'a) -> void { 
    array_push(arr, x)
}

fn print(x: 'a ToString) { print_string(str(x)) }
fn println(x: 'a ToString) {
    print_string(str(x) & newline)
}

fn format_append(s1: 'a ToString, s2: 'b ToString) {
    let s3 = str(s1)
    let s4 = str(s2)
    concat_strings(s3, s4)
}

"#;
