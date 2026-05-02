# Member Functions

A member function is a function attached to a type, callable with method syntax (`value.method()`). Add member functions to your own types — and even to built-in ones — with `extend`.

```
type Person = {
    first_name: string
    last_name: string
    age: int
}

extend Person {
    fn fullname(self) -> string {
        self.first_name .. " " .. self.last_name
    }
}

let p = Person("Arthur", "Pendragon", 15)
let name = p.fullname()    // "Arthur Pendragon"
```

The first parameter is named `self` and refers to the value the method is called on.

You can extend built-in types the same way. This is how `array<T>` gets its methods:

```
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

let arr = [0, 1, 2, 3, 4]
arr.push(5)
let l = arr.len()    // 6
```

### Two ways to call

When you write `p.fullname()`, the value before the dot is passed as the first argument. So these two calls do the same thing:

```
let name = p.fullname()
let name = Person.fullname(p)
```

Method syntax is the more common form, but the qualified form is useful when the type isn't obvious from context.

### Static methods

A member function with no `self` parameter is a static method — it's called on the type, not an instance. This is the usual way to write constructors:

```
extend Person {
    fn new(first: string, last: string) -> Person {
        Person(first, last, 0)
    }
}

let p = Person.new("Arthur", "Pendragon")
```
