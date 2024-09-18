use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::random;
use rdfp::d128;

fn bench_cmp(c: &mut Criterion) {
    let mut group = c.benchmark_group("d128");
    let lhs: Vec<d128> = (0..1024).map(|_| d128::from_bits(random())).collect();
    let rhs: Vec<d128> = (0..1024).map(|_| d128::from_bits(random())).collect();

    group.bench_function("const_eq/rand", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = lhs[i % lhs.len()];
            let rhs = rhs[i % rhs.len()];
            black_box(black_box(lhs).const_eq(black_box(rhs)));
            i = i.wrapping_add(1);
        });
    });

    group.bench_function("const_eq/eq", |b| {
        let mut i = 0;
        b.iter(|| {
            let x = lhs[i % lhs.len()];
            black_box(black_box(x).const_eq(black_box(x)));
            i = i.wrapping_add(1);
        });
    });

    group.bench_function("const_partial_cmp", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = lhs[i % lhs.len()];
            let rhs = rhs[i % rhs.len()];
            black_box(black_box(lhs).const_partial_cmp(black_box(rhs)));
            i = i.wrapping_add(1);
        });
    });

    group.bench_function("total_cmp", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = lhs[i % lhs.len()];
            let rhs = rhs[i % rhs.len()];
            black_box(black_box(lhs).total_cmp(black_box(rhs)));
            i = i.wrapping_add(1);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_cmp);
criterion_main!(benches);
