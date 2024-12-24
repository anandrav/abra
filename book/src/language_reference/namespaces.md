# Namespaces

Each Abra file has its own namespace. In order to use functions from another file, the `use` keyword must be used to bring them into scope.

cat.abra
```
fn meow() -> string {
    "nyan nyan nyan"
}
```

main.abra
```
use cat

meow()
```