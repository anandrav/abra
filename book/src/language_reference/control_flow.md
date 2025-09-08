# Control Flow

### If-Else

If-else expressions are used to choose between two pieces of code.
A boolean expression is given as an input. If the boolean value is true, the first piece of code is executed. If the
boolean value is false, then the second piece of code is executed.

```
// this code prints "hello"

let is_arriving = true
if is_arriving {
    println("hello")
} else {
    println("good bye")
}

```

If-else expressions can be chained in succession to check multiple conditions.

```
// this code prints "good night"

let is_morning = false
let is_afternoon = false
if is_morning {
    println("good morning")
} else if is_afternoon {
    println("good afternoon")
} else {
    println("good night")
}
```

If-else expressions always return a value.

```
let x = if true { 1 } else { 0 }    // x = 1
```

### Match

Match expressions test an expression against a set of patterns.
The first pattern that matches will have its corresponding

```
let n = 2
let s = match n {
    0 -> "zero"
    1 -> "one"
    2 -> "two"
    3 -> "three"
    _ -> "something else"
}
// s = "two"

```

### While loops

```
// this code prints
// "hellohellohello"

var n = 3
while n > 0 {
    print("hello")
    n = n - 1
}
```

### For loops

```
// this code prints "15"

let arr = [1, 2, 3, 4, 5]
var sum = 0

for n in arr {
    sum = sum + n
}

println(sum)
```