/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

pub const PRELUDE: &str = r#"
host fn print_string(s: string) -> void

fn not(b: bool) = if b false else true

// TODO: really need ability to just write Self instead of 'a Num implicitly being the principled type
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

interface Clone {
    fn clone: 'a Clone -> 'a Clone
}
extend array<'a> {
    fn len(self: array<'a>) -> int {
        array_length(self)
    }

    fn push(self: array<'a>, x: 'a) -> void {
        array_push(self, x)
    }

    fn pop(self: array<'a>) -> void {
        array_pop(self)
    }
}
implement Clone for array<'a Clone> {
    fn clone(arr: array<'a Clone>) -> array<'a Clone> {
        let new: array<'a> = []
        var i = 0
        while i < array_length(arr) {
            array_push(new, Clone.clone(arr[i]))
            i := i + 1
        }
        new
    }
}
implement Clone for void {
    fn clone(x) = x
}
implement Clone for int {
    fn clone(x) = x
}
implement Clone for float {
    fn clone(x) = x
}
implement Clone for bool {
    fn clone(x) = x
}
implement Clone for string {
    fn clone(x) = x
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
        "(" & ToString.str(a) & ", " & ToString.str(b) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString) {
    fn str(p) {
        let (a, b, c) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString) {
    fn str(p) {
        let (a, b, c, d) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString) {
    fn str(p) {
        let (a, b, c, d, e) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString) {
    fn str(p) {
        let (a, b, c, d, e, f) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ", " & ToString.str(j) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ", " & ToString.str(j) & ", " & ToString.str(k) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString, 'l ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k, l) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ", " & ToString.str(j) & ", " & ToString.str(k) & ", " & ToString.str(l) & ")"
    }
}

implement ToString for maybe<'y ToString,'n ToString> {
    fn str(m: maybe<'y ToString, 'n ToString>) {
        match m {
            .yes(y) -> "yes(" & y & ")",
            .no(n) -> "no(" & n & ")"
        }
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
        ToString.str(arr[idx])
    } else {
        ToString.str(arr[idx]) & ", " & array_to_string_helper(arr, idx + 1)
    }
}

fn print(x: 'a ToString) { print_string(ToString.str(x)) }
fn println(x: 'a ToString) {
    print_string(ToString.str(x) & newline)
}

fn format_append(s1: 'a ToString, s2: 'b ToString) {
    let s3 = ToString.str(s1)
    let s4 = ToString.str(s2)
    concat_strings(s3, s4)
}

interface Iterate {
    associatedtype Item
    associatedtype TheIterator impl Iterator<Item=Item>

    fn make_iterator: ('a Iterate) -> TheIterator
}

interface Iterator {
    associatedtype Item

    fn next: () -> maybe<Item,void>
}

implement Iterate for array<'T> {
    fn make_iterator(self) -> ArrayIterator<'T> {
        ArrayIterator(self, 0)
    }
}

type ArrayIterator<'T> = {
    arr: array<T>
    i: int
}
//
// implement Iterator for ArrayIterator<'T> {
//     fn next(self) -> maybe<'T,void> {
//         self.i := self.i + 1
//     }
// }

extend array<'a Equal> {
    fn find(self: array<'a Equal>, x: 'a Equal) -> maybe<int, void> {
        var i = 0
        while i < self.len() {
            if self[i] = x {
                return maybe.yes(i)
            }
            i := i + 1
        }
        maybe.no(())
    }

    fn contains(self: array<'a Equal>, x: 'a Equal) -> bool {
        match self.find(x) {
            maybe.yes(_) -> true,
            maybe.no(_) -> false,
        }
    }
}

"#;
