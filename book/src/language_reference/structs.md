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
