# Namespaces

Each Abra file has its own namespace determined by the name of the file and its parent directories (relative to the
entry point of the program).

For instance, if the entry point is `main.abra` and beside that main file, there is a `hat.abra` and a
`weapons/sword.abra`, like so:

```
- main.abra
- hat.abra
- [weapons]
    - sword.abra
    - spear.abra
```

and if the contents of those files are as follows

```
// hat.abra
fn wear() {
    println("you are wearing the hat")
}

fn pull_out_rabbit() {
    println("pulled a white rabbit out of the hat")
}
```

```
// sword.abra
fn swing() {
    println("SWOOSH")
}
```

```
// halberd.abra
fn swing() {
    println("SWOOSH")
}

fn stab() {
    println("SWOOSH")
}
```

Then the fully qualified names of those functions would be `hat.wear`, `weapons.sword.swing`, and
`weapons.halberd.swing` respectively.

By default, the functions in `hat.abra`, `sword.abra`, and `halberd.abra` are not accessible to `main.abra`.
In order to use functions from another file, the `use` keyword must be used to bring them into scope.

```
// main.abra

use hat
use weapons/sword

wear()
swing()
```

By default, the `use` keyword makes all symbols visible.
This is a convenient default, but it leads to name clashes in large projects.
To avoid name clashes, users can either:

1. Use the `use` keyword with the `except` keyword to exclude an unwanted symbol

    ```
    use weapons/sword
    use weapons/halberd except swing
    
    swing()         // sword.swing
    stab()          // halberd.stab
    ```

2. Explicitly import individual symbols

    ```
    use weapons/sword.swing
    use weapons/halberd.stab
    
    swing()         // sword.swing
    stab()          // halberd.stab
    ```

   Note: multiple symbols can be imported from a namespace like this:

    ```
    use weapons/halberd.(swing,stab)
    
    swing()         // halberd.swing
    stab()          // halberd.stab
    ```
3. Import symbols under a user-specified prefix

    ```
    use weapons/sword as sword
    use weapons/halberd as polearm
    
    sword.swing()           // sword.swing
    polearm.stab()          // halberd.stab
    ```
