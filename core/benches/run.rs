use abra_core::*;
use criterion::{criterion_group, criterion_main, Criterion};

fn fib() {
    let src = "func fibonacci(n) {
        match n {
            0 -> 0
            1 -> 1
            _ -> fibonacci(n-1) + fibonacci(n-2)
        }
    }
    fibonacci(12)";
    let _ = run(src);
}

fn run_benchmark(c: &mut Criterion) {
    c.bench_function("run fib", |b| b.iter(|| fib()));
}

criterion_group!(benches, run_benchmark);
criterion_main!(benches);
