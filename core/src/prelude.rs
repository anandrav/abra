pub const _PRELUDE: &str = r#"
fn not(b: bool) = if b false else true

interface Num {
    add: (self, self) -> self
    subtract: (self, self) -> self
    multiply: (self, self) -> self
    divide: (self, self) -> self
    power: (self, self) -> self
    less_than: (self, self) -> bool
    less_than_or_equal: (self, self) -> bool
    greater_than: (self, self) -> bool
    greater_than_or_equal: (self, self) -> bool
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

type list<'a> = nil | cons of ('a, list<'a>)

interface Equal {
    equal: (self, self) -> bool
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

implement Equal for list<'a Equal> {
    fn equal(a, b) {
        match (a, b) {
            (nil, nil) -> true
            (cons (~x, ~xs), cons (~y, ~ys)) -> {
                equal(x, y) and equal(xs, ys)
            }
            _ -> false
        }
    }
}

interface ToString {
    to_string: self -> string
}
implement ToString for string {
	fn to_string(s) = s
}
implement ToString for void {
	fn to_string(s) = "()"
}
implement ToString for int {
	fn to_string(n) = int_to_string(n)
}
implement ToString for bool {
	fn to_string(b) = if b "true" else "false"
}
implement ToString for float {
    fn to_string(f) = float_to_string(f)
}
implement ToString for ('a ToString, 'b ToString) {
    fn to_string(p) {
        let (a, b) = p
        "(" & to_string(a) & ", " & to_string(b) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString) {
    fn to_string(p) {
        let (a, b, c) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString) {
    fn to_string(p) {
        let (a, b, c, d) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString) {
    fn to_string(p) {
        let (a, b, c, d, e) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f, g) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f, g, h) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f, g, h, i) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f, g, h, i, j) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ", " & to_string(j) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f, g, h, i, j, k) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ", " & to_string(j) & ", " & to_string(k) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString, 'l ToString) {
    fn to_string(p) {
        let (a, b, c, d, e, f, g, h, i, j, k, l) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ", " & to_string(j) & ", " & to_string(k) & ", " & to_string(l) & ")"
    }
}

implement ToString for list<'a ToString> {
    fn to_string(xs) {
        let helper = xs -> {
            match xs {
                nil -> ""
                cons (~x, nil) -> {
                    to_string(x)
                }
                cons (~x, ~xs) -> {
                    to_string(x) & ", " & helper(xs)
                }
            }
        }
        "[| " & helper(xs) & " |]"
    }
}

implement ToString for array<'a ToString> {
    fn to_string(arr) {
       let helper = (arr, idx) -> {
            let l = array_length(arr)
            if idx = l {
                ""
            } else if idx = l - 1 {
                to_string(arr[idx])
            } else {
                to_string(arr[idx]) & ", " & helper(arr, idx + 1)
            }
        }
        "[ " & helper(arr, 0) & " ]"
    }
}

fn len(arr: array<'a>) -> int { 
    array_length(arr)
}

fn append(arr: array<'a>, x: 'a) -> void { 
    array_append(arr, x)
}

fn print(x: 'b ToString) { print_string(to_string(x)) }
fn println(x: 'b ToString) {
    print_string(to_string(x) & newline)
}

"#;
