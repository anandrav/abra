# Built-in Types

### int

A 64-bit signed integer.
Supports addition, subtraction, multiplication, division, and exponentiation operators.

```
let a = 5
let b = 2 + 2   // 4
let c = 2 * 3   // 6
let d = 5 - 2   // 3
let e = 12 / 3  // 4
let f = 13 / 3  // also 4
let g = 2 ^ 3   // 8

let n = (a + c / d) ^ 2 // 49
```

### float

A 64-bit signed floating point decimal number.
Supports addition, subtraction, multiplication, division, and exponentiation operators.

```
let pi = 3.14159
let e = 2.71828
```

### boolean

```
let shield_is_equipped = true
let sword_is_equipped = false
```

### string

Garbage-collected unicode text data.
Strings can be concatenated together using the `&` operator.

```
let name = "Merlin"
let message = name & " is a wizard." // "Merlin is a wizard."
```

### array<T>

A built-in dynamic array data structure. Supports random access (zero-indexed), pushing, and popping elements.
Arrays are homogenous; elements of the array must have the same type i.e. an array cannot mix `int` and `float`
elements, for instance.

```
let arr = [1, 2, 3, 4]  // create an array with some numbers
arr.push(5)             // arr = [1, 2, 3, 4, 5]
let n = arr.len()       // 5
let n = arr[2]          // 3
arr[2] := 49
let n = arr[2]          // 49
arr.pop()               // arr = [1, 2, 3, 4]
```

### tuples

- `(T, U)`
- `(T, U, V)`
- and so on...

A tuple is 2 or more values grouped together.
It is sometimes useful to group related values together.
For instance, a tuple of three floats could be used to represent a coordinate in 3d space.
Unlike arrays, tuples can have elements of different types.
Unlike arrays, tuples cannot have elements added or removed.

```
let pair_of_ints = (1, 2)
let coordinate_3d = (1.0, 2.0, -3.0)
let name_and_age = ("Lancelot", 19)
```

### void

Represents nothing and only has one value -- `()`.
This is useful as a return type for functions that donT return anything.
This is sometimes referred to as the "unit type" in other languages because it has a single value.

### never

The never type has zero values.
This is useful as a return type for a function which should never return.
For instance, the built-in `panic()` function, used to terminate the program in the case of an unrecoverable error, does
not return a value.
