use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::random;
use rdfp::{
    bid::idiv::{div128x64, reciprocal2x1},
    d128,
};

fn bench_div(c: &mut Criterion) {
    let mut group = c.benchmark_group("divide");

    let mut operands = [(0, 0, 0, 0); 1 << 14];
    for val in &mut operands {
        let u: u128 = random();
        let v: u64 = loop {
            let v = random();
            if v != 0 {
                break v;
            }
        };
        let rec = reciprocal2x1(v);
        *val = ((u >> 64) as u64, u as u64, v, rec);
    }

    group.bench_function("u128x64/baseline", |b| {
        const fn quorem(u: u128, v: u64) -> (u128, u64) {
            let q = u / (v as u128);
            let r = u % (v as u128);
            (q, r as u64)
        }
        let mut i = 0;
        b.iter(|| {
            let (u1, u0, v, rec) = operands[i % operands.len()];
            let u = ((u1 as u128) << 64) | (u0 as u128);
            black_box(quorem(black_box(u), black_box(v)));
            i += 1;
        });
    });
    group.bench_function("u128x64/div128x64", |b| {
        let mut i = 0;
        b.iter(|| {
            let (u1, u0, v, rec) = operands[i % operands.len()];
            black_box(div128x64(
                black_box(u1),
                black_box(u0),
                black_box(v),
                black_box(rec),
            ));
            i += 1;
        });
    });

    group.finish();
}

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

criterion_group!(benches, bench_cmp, bench_div);
criterion_main!(benches);
