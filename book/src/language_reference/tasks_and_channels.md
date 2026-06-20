# Tasks and Channels

Sometimes you want your program to start one piece of work and then keep going. For example, a game might listen for input while something else is loading, or a program might start a slow calculation and wait for the answer later.

In Abra, use `task` to start another piece of code:

```
task {
    println("hello from the task")
}

println("hello from the main program")
```

The code inside the `task` can run alongside the code after it. Abra's scheduler decides when each task gets a turn, so you should not write code that depends on which `println` happens first.

A task does not return a value to the place where it was created. If you want a task to send a value back, use a channel.

### Capturing values

A task can use values from the surrounding code:

```
let name = "Ada"

task {
    println("hello, " .. name)
}
```

When a task starts, Abra gives it its own copy of the values it uses. This is important for arrays, structs, strings, and other data that could otherwise be changed from two places at once.

```
let numbers = [1, 2, 3]
let done: channel<int> = channel()

task {
    numbers.push(4)
    done.write(numbers.len())
}

println(numbers.len())   // 3
println(done.read())     // 4
```

The task gets a copy of `numbers`, so changing it inside the task does not change `numbers` in the main program.

### Channels

A channel is a way for tasks to pass messages to each other. A channel has a type, so a `channel<string>` can carry strings, and a `channel<int>` can carry integers.

```
let messages: channel<string> = channel()
```

Use `.write(...)` to send a value into a channel, and `.read()` to take a value out:

```
messages.write("done")
let msg = messages.read()
```

If a task tries to read from an empty channel, it waits until some other task writes a value.

Channels are also how you intentionally share something between tasks. Ordinary captured values are copied, but a captured channel still points to the same channel.

### Sending a result back

Here is a task that doubles a number and sends the answer back:

```
let answers: channel<int> = channel()

task {
    let n = 21
    answers.write(n * 2)
}

println(answers.read())   // 42
```

The main program waits at `answers.read()` until the task writes the answer.

You can also use one channel for work going into a task, and another channel for results coming back:

```
let jobs: channel<int> = channel()
let results: channel<int> = channel()

task {
    for _ in 10 {
        let n = jobs.read()
        results.write(n * 2)
    }
}

for i in 10 {
    jobs.write(i)
}

var sum = 0
for _ in 10 {
    sum += results.read()
}

println(sum)   // 90
```

### Waiting for a task

The main program does not automatically wait for every task to finish. When the main program is done, the whole program is done.

If the main program needs to wait for a task, have the task send a message:

```
let done: channel<void> = channel()

task {
    println("working")
    done.write(nil)
}

done.read()
println("finished")
```

This pattern is common: start a task, let it do work, and use a channel when you need to hear back from it.
