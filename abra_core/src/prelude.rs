/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

pub const PRELUDE: &str = r#"#host fn print_string(s: string) -> void

#host fn readline() -> string

#host fn get_args() -> array<string>

interface Num {
    fn add(a: Self, b: Self) -> Self
    fn subtract(a: Self, b: Self) -> Self
    fn multiply(a: Self, b: Self) -> Self
    fn divide(a: Self, b: Self) -> Self
    fn power(a: Self, b: Self) -> Self
}

implement Num for int {
    fn add(a, b) = add_int(a, b)
    fn subtract(a, b) = subtract_int(a, b)
    fn multiply(a, b) = multiply_int(a, b)
    fn divide(a, b) = divide_int(a, b)
    fn power(a, b) = power_int(a, b)
}

implement Num for float {
    fn add(a, b) = add_float(a, b)
    fn subtract(a, b) = subtract_float(a, b)
    fn multiply(a, b) = multiply_float(a, b)
    fn divide(a, b) = divide_float(a, b)
    fn power(a, b) = power_float(a, b)
}

type option<T> = some(T) | none

fn unwrap(m: option<T>) -> T {
    match m {
        .some(x) -> x
        .none -> panic("cannot unwrap option.none")
    }
}

interface Equal {
    fn equal(a: Self, b: Self) -> bool
}
implement Equal for void {
    fn equal(a, b) = true
}
implement Equal for int {
    fn equal(a, b) = equal_int(a, b)
}
implement Equal for float {
    fn equal(a, b) = equal_float(a, b)
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

// TODO implement Equal for tuples... do it at the bottom of the prelude

interface Ord {
    fn less_than(a: Self, b: Self) -> bool
    fn less_than_or_equal(a: Self, b: Self) -> bool
    fn greater_than(a: Self, b: Self) -> bool
    fn greater_than_or_equal(a: Self, b: Self) -> bool
}

implement Ord for int {
    fn less_than(a, b) = less_than_int(a, b)
    fn less_than_or_equal(a, b) = less_than_or_equal_int(a, b)
    fn greater_than(a, b) = greater_than_int(a, b)
    fn greater_than_or_equal(a, b) = greater_than_or_equal_int(a, b)
}

implement Ord for float {
    fn less_than(a, b) = less_than_float(a, b)
    fn less_than_or_equal(a, b) = less_than_or_equal_float(a, b)
    fn greater_than(a, b) = greater_than_float(a, b)
    fn greater_than_or_equal(a, b) = greater_than_or_equal_float(a, b)
}

implement Ord for void {
    fn less_than(a, b) = false
    fn less_than_or_equal(a, b) = true
    fn greater_than(a, b) = false
    fn greater_than_or_equal(a, b) = true
}

implement Ord for bool {
    fn less_than(a, b) = (not a) and b
    fn less_than_or_equal(a, b) = not (a and not b)
    fn greater_than(a, b) = a and (not b)
    fn greater_than_or_equal(a, b) = a and not b
}

implement Ord for (T1 Ord, T2 Ord) {
    fn less_than(a, b) {
        let (a1, a2) = a
        let (b1, b2) = b

        if Ord.less_than(a1, b1) return true
        if Ord.greater_than(a1, b1) return false

        Ord.less_than(a2, b2)
    }

    fn less_than_or_equal(a, b) {
        let (a1, a2) = a
        let (b1, b2) = b

        if Ord.less_than(a1, b1) return true
        if Ord.greater_than(a1, b1) return false

        Ord.less_than_or_equal(a2, b2)
    }

    fn greater_than(a, b) {
        let (a1, a2) = a
        let (b1, b2) = b

        if Ord.greater_than(a1, b1) return true
        if Ord.less_than(a1, b1) return false

        Ord.greater_than(a2, b2)
    }

    fn greater_than_or_equal(a, b) {
        let (a1, a2) = a
        let (b1, b2) = b

        if Ord.greater_than(a1, b1) return true
        if Ord.less_than(a1, b1) return false

        Ord.greater_than_or_equal(a2, b2)
    }
}

interface Clone {
    fn clone(x: Self) -> Self
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
    fn str(s: Self) -> string
}
implement ToString for string {
	fn str(s) = s
}
implement ToString for void {
	fn str(s) = "nil"
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
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString) {
    fn str(p) {
        let (a, b, c) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString) {
    fn str(p) {
        let (a, b, c, d) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString) {
    fn str(p) {
        let (a, b, c, d, e) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ", " .. ToString.str(g) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ", " .. ToString.str(g) .. ", " .. ToString.str(h) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ", " .. ToString.str(g) .. ", " .. ToString.str(h) .. ", " .. ToString.str(i) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString, T10 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ", " .. ToString.str(g) .. ", " .. ToString.str(h) .. ", " .. ToString.str(i) .. ", " .. ToString.str(j) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString, T10 ToString, T11 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ", " .. ToString.str(g) .. ", " .. ToString.str(h) .. ", " .. ToString.str(i) .. ", " .. ToString.str(j) .. ", " .. ToString.str(k) .. ")"
    }
}
implement ToString for (T1 ToString, T2 ToString, T3 ToString, T4 ToString, T5 ToString, T6 ToString, T7 ToString, T8 ToString, T9 ToString, T10 ToString, T11 ToString, T12 ToString) {
    fn str(p) {
        let (a, b, c, d, e, f, g, h, i, j, k, l) = p
        "(" .. ToString.str(a) .. ", " .. ToString.str(b) .. ", " .. ToString.str(c) .. ", " .. ToString.str(d) .. ", " .. ToString.str(e) .. ", " .. ToString.str(f) .. ", " .. ToString.str(g) .. ", " .. ToString.str(h) .. ", " .. ToString.str(i) .. ", " .. ToString.str(j) .. ", " .. ToString.str(k) .. ", " .. ToString.str(l) .. ")"
    }
}

implement ToString for option<T ToString> {
    fn str(m: option<T ToString>) {
        match m {
            .some(x) -> "some(" .. x .. ")"
            .none -> "none"
        }
    }
}

implement ToString for array<T ToString> {
    fn str(arr) {
        "[ " .. array_to_string_helper(arr, 0) .. " ]"
    }
}

fn array_to_string_helper(arr: array<T ToString>, idx: int) {
    let l = array_length(arr)
    if idx == l {
        ""
    } else if idx == l - 1 {
        ToString.str(arr[idx])
    } else {
        ToString.str(arr[idx]) .. ", " .. array_to_string_helper(arr, idx + 1)
    }
}

fn print(x: T ToString) { print_string(ToString.str(x)) }
fn println(x: T ToString) {
    print_string(ToString.str(x) .. "\n")
}

fn format_append(s1: T1 ToString, s2: T2 ToString) {
    concat_strings(ToString.str(s1), ToString.str(s2))
}

interface Iterable {
    outputtype IterableItem
    outputtype Iter impl Iterator<IteratorItem=IterableItem>

    fn make_iterator(self: Self) -> Iter
}

implement Iterable for array<T> {
    fn make_iterator(self) -> ArrayIterator<T> {
        ArrayIterator(self, 0)
    }
}

interface Iterator {
    outputtype IteratorItem

    fn next(self: Self) -> option<IteratorItem>
}

type ArrayIterator<P> = {
    arr: array<P>
    i: int
}

implement Iterator for ArrayIterator<V> {
    fn next(self: ArrayIterator<V>) -> option<V> {
        if self.i == self.arr.len() {
            .none
        } else {
            let ret = option.some(self.arr[self.i])
            self.i = self.i + 1
            ret
        }
    }
}

type range = {
    begin: int
    end: int
}

extend range {
    fn contains(self, i: int) -> bool {
        i >= self.begin and i < self.end
    }
}

fn range_inclusive(begin: int, end: int) -> range {
    range(begin, end+1)
}

implement Iterable for range {
    fn make_iterator(self) -> RangeIterator {
        RangeIterator(self.begin, self.end)
    }
}

type RangeIterator = {
    begin: int
    end: int
}

implement Iterator for RangeIterator {
    fn next(self) -> option<int> {
        if self.begin >= self.end {
            .none
        } else {
            let ret = self.begin
            self.begin = self.begin + 1
            .some(ret)
        }
    }
}

implement Iterable for int {
    fn make_iterator(self) -> RangeIterator {
        RangeIterator(0, self)
    }
}

extend array<T> {
    fn len(self) -> int {
        array_length(self)
    }

    fn is_empty(self) -> bool {
        self.len() == 0
    }

    fn push(self, x: T) -> void {
        array_push(self, x)
    }

    fn pop(self) -> T {
        array_pop(self)
    }

    fn swap(self, i, j) {
      let temp = self[i]
      self[i] = self[j]
      self[j] = temp
    }

    fn remove(self, index: int) -> void {
        self.swap(index, self.len()-1)
        self.pop()
        nil
    }

    fn bounds(self) -> range {
        range(0, self.len())
    }
}

extend array<T Equal> {
    fn find(self, x: T Equal) -> option<int> {
        for i in self.len() {
            if self[i] == x {
                return .some(i)
            }
        }
        .none
    }

    fn contains(self, x: T Equal) -> bool {
        match self.find(x) {
            .some(_) -> true
            .none -> false
        }
    }
}

extend array<T Ord> {
    fn sort(self) -> void {
        let n = self.len()
        let RUN = 32

        var i = 0
        while i < n {
            let end = if i + RUN - 1 < n - 1 { i + RUN - 1 } else { n - 1 }
            self.insertion_sort(i, end)
            i = i + RUN
        }

        let temp = []
        var size = RUN

        while size < n {
            var left = 0
            while left < n {
                let mid = left + size - 1
                let right = if left + 2 * size - 1 < n - 1 {
                    left + 2 * size - 1
                } else {
                    n - 1
                }

                if mid < right {
                    self.merge(left, mid, right, temp)
                }

                left = left + 2 * size
            }
            size = size * 2
        }
    }

    fn insertion_sort(self, left, right) {
        var i = left + 1
        while i <= right {
            let key = self[i]
            var j = i - 1

            while j >= left and self[j] > key {
                self[j + 1] = self[j]
                j = j - 1
            }
            self[j + 1] = key
            i = i + 1
        }
    }

    fn merge(self, left: int, mid: int, right: int, temp: array<T>) {
        let n1 = mid - left + 1
        var i = 0
        while i < n1 {
            temp.push(self[left + i])
            i = i + 1
        }

        var i_curr = 0
        var j = mid + 1
        var k = left

        while i_curr < n1 and j <= right {
            if temp[i_curr] <= self[j] {
                self[k] = temp[i_curr]
                i_curr = i_curr + 1
            } else {
                self[k] = self[j]
                j = j + 1
            }
            k = k + 1
        }

        while i_curr < n1 {
            self[k] = temp[i_curr]
            i_curr = i_curr + 1
            k = k + 1
        }

        var cleanup = 0
        while cleanup < n1 {
            temp.pop()
            cleanup = cleanup + 1
        }
    }
}

"#;
