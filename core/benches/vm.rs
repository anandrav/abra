use abra_core::FileProviderDefault;
use abra_core::compile_bytecode;
use abra_core::effects::DefaultEffects;
use abra_core::effects::EffectTrait;
use abra_core::source_files_single;
use abra_core::vm::Vm;
use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};

// Generalized function for benchmarking Abra programs
fn run_benchmark(c: &mut Criterion, name: &str, src: &str) {
    let sources = source_files_single(src);
    let program = compile_bytecode(
        sources,
        DefaultEffects::enumerate(),
        FileProviderDefault::todo_get_rid_of_this(),
    )
    .unwrap();

    c.bench_function(name, |b| {
        b.iter_batched(
            || Vm::new(program.clone()), // Prepare a new VM instance
            |mut vm| {
                vm.run();
                black_box(vm.top());
            },
            BatchSize::SmallInput, // Reasonable batch size
        );
    });
}

// Fibonacci (Recursive)
pub fn fib_benchmark(c: &mut Criterion) {
    let src = r#"
fn fib(n) {
    match n {
        0 -> 0
        1 -> 1
        _ -> fib(n-1) + fib(n-2)
    }
}   
fib(20)
"#;
    run_benchmark(c, "fibonacci_recursive", src);
}

// Sum loop
pub fn sum_benchmark(c: &mut Criterion) {
    let src = r#"
let sum = 0
var i = 0
while i < 100000 {
    sum <- sum + i
    i <- i + 1
}
sum
"#;
    run_benchmark(c, "sum_loop", src);
}

// Ackermann function
pub fn ack_benchmark(c: &mut Criterion) {
    let src = r#"
fn ack(m, n) {
    if m = 0 { n + 1 }
    else if n = 0 { ack(m - 1, 1) }
    else  { ack(m - 1, ack(m, n - 1)) }
}
ack(3, 6)
"#;
    run_benchmark(c, "ackermann", src);
}

// pub fn random_benchmark(c: &mut Criterion) {
//     let src = r#"
// let seed = 12345
// let a = 1664525
// let c = 1013904223
// let m = 2^32
// fn rng(n) {
//     if n = 0 {
//         seed
//     } else {
//         (a * rng(n - 1) + c) % m
// }
// }
// rng(100000)
// "#;
//     run_benchmark(c, "random_lcg", src);
// }

// // Sieve of Eratosthenes
// pub fn sieve_benchmark(c: &mut Criterion) {
//     let src = r#"
// let limit = 10000
// let primes = [true for _ in 0..=limit]
// for p in 2..=limit {
//     if primes[p] {
//         for i in (p * p)..=limit by p {
//             primes[i] := false
//         }
//     }
// }
// "#;
//     run_benchmark(c, "sieve_of_eratosthenes", src);
// }

// Heap sort
// pub fn heapsort_benchmark(c: &mut Criterion) {
//     let src = r#"
// fn heapify(arr, n, i) {
//     let largest = i
//     let left = 2 * i + 1
//     let right = 2 * i + 2

//     if left < n && arr[left] > arr[largest] {
//         largest := left
//     }
//     if right < n && arr[right] > arr[largest] {
//         largest := right
//     }
//     if largest != i {
//         let tmp = arr[i]
//         arr[i] := arr[largest]
//         arr[largest] := tmp
//         heapify(arr, n, largest)
//     }
// }

// fn heapsort(arr) {
//     let n = arr.len()
//     for i in (n / 2 - 1)..=-1 {
//         heapify(arr, n, i)
//     }
//     for i in (n - 1)..=0 {
//         let tmp = arr[0]
//         arr[0] := arr[i]
//         arr[i] := tmp
//         heapify(arr, i, 0)
//     }
// }
// let arr = [5, 3, 8, 4, 2, 7, 1, 9, 6]
// heapsort(arr)
// "#;
//     run_benchmark(c, "heap_sort", src);
// }

// // Matrix multiplication
// pub fn matrix_benchmark(c: &mut Criterion) {
//     let src = r#"
// let A = [[1, 2], [3, 4]]
// let B = [[5, 6], [7, 8]]
// let C = [[0, 0], [0, 0]]

// for i in 0..2 {
//     for j in 0..2 {
//         for k in 0..2 {
//             C[i][j] := C[i][j] + A[i][k] * B[k][j]
//         }
//     }
// }
// "#;
//     run_benchmark(c, "matrix_multiplication", src);
// }

// Register all benchmarks
criterion_group!(
    benches,
    fib_benchmark,
    sum_benchmark,
    ack_benchmark,
    // random_benchmark,
    // sieve_benchmark,
    // heapsort_benchmark,
    // matrix_benchmark
);
criterion_main!(benches);
