use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::{prelude::*, random, thread_rng};
use rdfp::{
    bid::{
        arith128, arith64,
        idiv::{Divisor128, Divisor64},
    },
    d128,
};

fn bench_arith64(c: &mut Criterion) {
    let mut group = c.benchmark_group("arith64");
    group.bench_function("shr", |b| {
        let mut vals = [(0, 0); 1 << 14];
        for val in &mut vals {
            *val = (random(), thread_rng().gen_range(0..=17))
        }
        let mut i = 0;
        b.iter(|| {
            let (x, n) = vals[i % vals.len()];
            black_box(arith64::shr(black_box(x), black_box(n)));
            i += 1;
        });
    });
    group.finish();
}

fn bench_arith128(c: &mut Criterion) {
    let mut group = c.benchmark_group("arith128");
    group.bench_function("shr", |b| {
        let mut vals = [(0, 0); 1 << 14];
        for val in &mut vals {
            *val = (random(), thread_rng().gen_range(0..=34))
        }
        let mut i = 0;
        b.iter(|| {
            let (x, n) = vals[i % vals.len()];
            black_box(arith128::shr(black_box(x), black_box(n)));
            i += 1;
        });
    });
    group.finish();
}

fn bench_div(c: &mut Criterion) {
    let mut group = c.benchmark_group("divide");

    let mut operands = [(0, 0, Divisor128::uninit()); 1 << 14];
    for val in &mut operands {
        let u = random();
        let mut v = random();
        if v == 0 {
            v = 1;
        }
        let d = Divisor128::new(u);
        *val = (u, v, d);
    }

    group.bench_function("u128/baseline", |b| {
        const fn quorem(u: u128, v: u128) -> (u128, u128) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        let mut i = 0;
        b.iter(|| {
            let (u, v, _) = operands[i % operands.len()];
            black_box(quorem(black_box(u), black_box(v)));
            i += 1;
        });
    });
    group.bench_function("u128/reciprocal", |b| {
        let mut i = 0;
        b.iter(|| {
            let (u, _, d) = operands[i % operands.len()];
            black_box(d.quorem(black_box(u)));
            i += 1;
        });
    });

    let mut operands = [(0, 0, Divisor64::uninit()); 1 << 14];
    for val in &mut operands {
        let u = random();
        let mut v = random();
        if v == 0 {
            v = 1;
        }
        let d = Divisor64::new(u);
        *val = (u, v, d);
    }

    group.bench_function("u64/baseline", |b| {
        const fn quorem(u: u64, v: u64) -> (u64, u64) {
            let q = u / v;
            let r = u % v;
            (q, r)
        }
        let mut i = 0;
        b.iter(|| {
            let (u, v, _) = operands[i % operands.len()];
            black_box(quorem(black_box(u), black_box(v)));
            i += 1;
        });
    });
    group.bench_function("u64/reciprocal", |b| {
        let mut i = 0;
        b.iter(|| {
            let (u, _, d) = operands[i % operands.len()];
            black_box(d.quorem(black_box(u)));
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

criterion_group!(benches, bench_arith128, bench_arith64, bench_cmp, bench_div);
criterion_main!(benches);
