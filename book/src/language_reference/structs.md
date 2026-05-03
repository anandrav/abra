# Structs

A struct groups several named fields into one value. Use them when you have a few related pieces of data that belong together — coordinates, user records, configuration, anything where naming the fields makes the code clearer.

```
type Person = {
    first_name: string
    last_name: string
    age: int
}
```

Construct an instance by calling the type name like a function. Arguments go in field order:

```
let frank = Person("Frank", "Smith", 34)
```

Read fields with `.`:

```
let fullname = frank.first_name .. " " .. frank.last_name
// "Frank Smith"
```

And update them the same way:

```
frank.age = frank.age + 1   // 35
```

### Default field values

A field can have a default value. When constructing the struct, callers can leave any trailing field off:

```
type Greeter = {
    name: string
    greeting: string = "Hello"
    excited: bool = false
}

extend Greeter {
    fn greet(self) {
        let punct = if self.excited { "!" } else { "." }
        println(self.greeting .. ", " .. self.name .. punct)
    }
}

Greeter("Alice").greet()                         // "Hello, Alice."
Greeter("Bob", "Howdy").greet()                  // "Howdy, Bob."
```

### Named field arguments

You can also pass a field by name, which lets you skip past fields that have defaults:

```
Greeter("Carol", excited = true).greet()                       // "Hello, Carol!"
Greeter("Dave", greeting = "Hi", excited = true).greet()       // "Hi, Dave!"
```

Named arguments must come after all positional arguments.

### Generic structs

A struct can take a type parameter, so it works with any element type:

```
type Ref<T> = {
    value: T
}

let int_ref = Ref(42)         // Ref<int>
let str_ref = Ref("hello")    // Ref<string>
```

See [Generics](./generics.md) for more.

### Adding behavior

To attach methods to a struct, use [`extend`](./member_functions.md). To make it work with `==`, sorting, printing, or other operators, [implement an interface](./interfaces.md) for it.
