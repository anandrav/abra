## Error Handling

Abra uses two prelude types to represent operations that can fail: `option` (for "value or nothing") and `result` (for "value or error").

### option

Use `option<T>` when the only failure mode is "no value":

```
type option<T> =
  | some(T)
  | none
```

```
fn safe_divide(a: float, b: float) -> option<float> {
    if b == 0.0 {
        .none
    } else {
        .some(a / b)
    }
}
```

### result

Use `result<T, E>` when failure carries information about what went wrong:

```
type result<T, E> =
  | ok(T)
  | err(E)
```

Most standard library functions that can fail return a `result`. For example, `core/fs::read` returns `result<string, FsError>`:

```
use core/fs

match read("greeting.txt") {
    .ok(contents) -> println(contents)
    .err(e) -> println("could not read: " .. e)
}
```

### Unwrap (`!`)

The unwrap operator `!` extracts the value from a `some` or `ok`, panicking if it's a `none` or `err`. Use it when you know the value is present.

```
let a = "10".to_int()!     // panics if not a valid int
let b = "5".to_int()!
println(a + b)             // prints "15"
```

`!` is syntactic sugar for the `Unwrap` interface, which is implemented for both `option` and `result`.

### Try (`?`)

The try operator `?` propagates a `none` or `err` to the caller, returning early. The enclosing function must return a compatible type.

```
use core/fs

fn concat_files(a: string, b: string) -> result<string, FsError> {
    let first = read(a)?       // early-return if read fails
    let second = read(b)?
    .ok(first .. second)
}
```

If `read(a)` returns `.err(e)`, `concat_files` returns `.err(e)` immediately and the rest of the function does not run.

`?` works with `option` too, but the enclosing function must return an `option`:

```
fn first_two_chars(s: string) -> option<string> {
    let chars = s.chars()
    if chars.len() < 2 {
        return .none
    }
    .some(chars[0] .. chars[1])
}
```

### Converting between error types

When you want to bubble up an error but the error types don't match, use `result.map_err` to convert:

```
use core/fs

fn run() -> result<string, string> {
    let contents = read("file.txt").map_err(e -> e.str())?
    .ok(contents)
}
```

Here `read` returns `result<string, FsError>` but `run` returns `result<string, string>`, so we convert `FsError` to `string` before propagating.
