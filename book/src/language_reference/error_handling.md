## Error Handling

It is recommended to use the `maybe` type defined in the standard library as a return type for functions that can fail.
The `maybe` type is the same as the `Result` type in Rust or the `Either` type in Haskell.

```
type maybe<'T,'E> =
  | yes('T)
  | no('E)
```

```
fn safe_divide(a: float, b: float) -> maybe<float, void> {
    if b = 0.0 {
        .no(())
    } else {
        .yes(a / b)
    }
}
```

For convenience, you can use the unwrap operator `!` to forcibly get the value from the `yes` case, or invoke `panic()`
if it's the `no` case. This is useful if you know that the result is guaranteed to be a success.
The `!` operator is syntactic sugar for calling `.unwrap()` on some value.

```
// assume string_to_int: string -> maybe<int, void>

let a = string_to_int("10")!
let b = string_to_int("5")!
println(a + b)

// prints "15"
```
