# Functions

A function takes 0 or more arguments and returns a single value.

```
fn increment_if_true(n: int, condition: boolean) -> int {
    if condition {
        n + 1
    } else {
        n
    }
}
```

A function always returns the value of its body. If the body of a function is a block of statements, the last statement/expression of the block is the return value of the function. There are no explicit return statements and therefore no early return statements.