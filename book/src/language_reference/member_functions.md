## Member Functions

For convenience, you can define member functions on both user-defined and built-in types.

```
type Person = {
    first_name: string,
    last_name: string,
    age: int,
}

extend Person {
    fn fullname(self) -> string {
        self.first_name & self.last_name
    }
}

...

let p = Person("Arthur", "Pendragon", 15)
let name = p.fullname() // "Arthur Pendragon"
```

```
extend array<'T> {
    fn len(self: array<'T>) -> int {
        array_length(self)
    }

    fn push(self: array<'T>, x: 'T) -> void {
        array_push(self, x)
    }

    fn pop(self: array<'T>) -> void {
        array_pop(self)
    }
}

...

let arr = [0, 1, 2, 3, 4]
arr.push(5)
let l = arr.len() // 6
```

In the examples above, a member function is invoked on a variable using the dot `.` operator.
The variable is passed as the first argument to the member function.

Member functions can also be invoked on the type itself.
In that case, the first argument to the function is passed in the parentheses.

```
let p = Person("Arthur", "Pendragon", 15)
let name = Person.fullname(p)

let arr = [1, 2, 3, 4]
array.push(arr)
let l = array.len(arr) // 6
```