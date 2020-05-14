use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::collections::{HashMap, HashSet};
use std::time::Duration;

use backtrack_rs::n_queens::*;
use backtrack_rs::*;

fn bench_backtracking(c: &mut Criterion) {
  let mut group = c.benchmark_group("Backtracking");
  group.sample_size(10);
  group.measurement_time(Duration::from_secs(20));

  for n in [4, 8].iter() {
    let csp = n_queens_csp(*n);

    group.bench_with_input(BenchmarkId::new("Backtrack (Recursive)", n), &csp, |b, _n| {
      b.iter(|| backtrack(HashMap::new(), &csp.variables, &csp))
    });

    group.bench_with_input(BenchmarkId::new("Backtrack (Recursive Cache)", n), &csp, |b, _n| {
      b.iter(|| backtrack_cache(HashMap::new(), &csp.variables, &csp, &mut (HashSet::new())))
    });

    group.bench_with_input(BenchmarkId::new("Backtrack (Iterative)", n), &csp, |b, _n| {
      b.iter(|| backtrack_iter(HashMap::new(), &csp.variables, &csp))
    });
  }

  group.finish();
}

criterion_group!(benches, bench_backtracking);
criterion_main!(benches);
