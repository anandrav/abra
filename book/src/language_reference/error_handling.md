## Error Handling

It is recommended to use the `option` type defined in the standard library as a return type for functions that can fail.

```
type option<'T> =
  | some of 'T
  | none
```

```
fn safe_divide(a: float, b: float) -> option<float> {
    if b = 0.0 {
        .none
    } else {
        .some(a / b)
    }
}
```

For convenience, you can use the unwrap operator `!` to forcibly get the value from the `some` case, or invoke `panic()`
if it's the `none` case. This is useful if you know that the result is guaranteed to be a success.
The `!` operator is syntactic sugar for calling `.unwrap()` on some value.

```
// assume string_to_int: string -> option<int>

let a = string_to_int("10")!
let b = string_to_int("5")!
println(a + b)

// prints "15"
```
