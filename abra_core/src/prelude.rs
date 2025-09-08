/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

pub const PRELUDE: &str = r#"
host fn print_string(s: string) -> void
host fn readline() -> string
//host fn get_args() -> array<string>

fn not(b: bool) = if b false else true

interface Num {
    fn add: (Self, Self) -> Self
    fn subtract: (Self, Self) -> Self
    fn multiply: (Self, Self) -> Self
    fn divide: (Self, Self) -> Self
    fn power: (Self, Self) -> Self
    fn less_than: (Self, Self) -> bool
    fn less_than_or_equal: (Self, Self) -> bool
    fn greater_than: (Self, Self) -> bool
    fn greater_than_or_equal: (Self, Self) -> bool
}

implement Num for int {
    fn add(a, b) = add_int(a, b)
    fn subtract(a, b) = subtract_int(a, b)
    fn multiply(a, b) = multiply_int(a, b)
    fn divide(a, b) = divide_int(a, b)
    fn power(a, b) = power_int(a, b)
    fn less_than(a, b) = less_than_int(a, b)
    fn less_than_or_equal(a, b) = (a < b) or (a == b)
    fn greater_than(a, b) = not(a < b) and not(a == b)
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

type option<T> = some of T | none

fn unwrap(m: option<T>) -> T {
    match m {
        .some(x) -> x,
        .none -> panic("cannot unwrap option.none")
    }
}

interface Equal {
    fn equal: (Self, Self) -> bool
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
    fn clone: Self -> Self
}

implement Clone for array<T Clone> {
    fn clone(arr: array<T Clone>) -> array<T Clone> {
        let new = []
        for x in arr {
            new.push(Clone.clone(x)) // TODO: should be able to do x.clone() here
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
    fn str: Self -> string
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
implement ToString for (T1 ToString, T2 ToString) {
    fn str(p) {
        let (a, b) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString) {
    fn str(p) {
        let (a, b, c) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString) {
    fn str(p) {
        let (a, b, c, d) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString) {
    fn str(p) {
        let (a, b, c, d, e) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString, T10 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ", " & ToString.str(j) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString, T10 ToString, T11 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ", " & ToString.str(j) & ", " & ToString.str(k) & ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString, T10 ToString, T11 ToString, T12 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k, l) = p
        "(" & ToString.str(a) & ", " & ToString.str(b) & ", " & ToString.str(c) & ", " & ToString.str(d) & ", " & ToString.str(e) & ", " & ToString.str(f) & ", " & ToString.str(g) & ", " & ToString.str(h) & ", " & ToString.str(i) & ", " & ToString.str(j) & ", " & ToString.str(k) & ", " & ToString.str(l) & ")"
    }
}

implement ToString for option<T ToString> {
    fn str(m: option<T ToString>) {
        match m {
            .some(x) -> "some(" & x & ")",
            .none -> "none"
        }
    }
}

implement ToString for array<T ToString> {
    fn str(arr) {
        "[ " & array_to_string_helper(arr, 0) & " ]"
    }
}

fn array_to_string_helper(arr: array<T ToString>, idx: int) {
    let l = array_length(arr)
    if idx == l {
        ""
    } else if idx == l - 1 {
        ToString.str(arr[idx])
    } else {
        ToString.str(arr[idx]) & ", " & array_to_string_helper(arr, idx + 1)
    }
}

fn print(x: T ToString) { print_string(ToString.str(x)) }
fn println(x: T ToString) {
    print_string(ToString.str(x) & newline)
}

fn format_append(s1: T1 ToString, s2: T2 ToString) {
    let s3 = ToString.str(s1)
    let s4 = ToString.str(s2)
    concat_strings(s3, s4)
}

interface Iterable {
    outputtype IterableItem
    outputtype Iter impl Iterator<IteratorItem=IterableItem>

    fn make_iterator: (Self) -> Iter
}

implement Iterable for array<T> {
    fn make_iterator(self) -> ArrayIterator<T> {
        ArrayIterator(self, 0)
    }
}

interface Iterator {
    outputtype IteratorItem

    fn next: (Self) -> option<IteratorItem>
}

type ArrayIterator<U> = {
    arr: array<U>
    i: int
}

implement Iterator for ArrayIterator<U> {
    fn next(self) -> option<U> {
        if self.i == self.arr.len() {
            option.none
        } else {
            let ret = option.some(self.arr[self.i])
            self.i = self.i + 1
            ret
        }
    }
}

fn range(hi: int) -> array<int> {
    let ret = []
    var lo = 0
    while lo < hi {
        ret.push(lo)
        lo = lo + 1
    }
    ret
}

extend array<T> {
    fn len(self) -> int {
        array_length(self)
    }

    fn push(self, x: T) -> void {
        array_push(self, x)
    }

    fn pop(self) -> void {
        array_pop(self)
    }
}

extend array<T Equal> {
    fn find(self, x: T Equal) -> option<int> {
        for i in range(self.len()) {
            if self[i] == x {
                return option.some(i)
            }
        }
        option.none
    }

    fn contains(self, x: T Equal) -> bool {
        match self.find(x) {
            option.some(_) -> true,
            option.none -> false,
        }
    }
}

"#;
