use std::array;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use inteldfp as dfp;
use rand::{prelude::*, random, thread_rng};
use rdfp::{
    bid::{
        arith128, arith64,
        idiv::{Divisor128, Divisor64},
    },
    d128, d64,
};

fn bench_bid64(c: &mut Criterion) {
    let min = d64::MIN_EXP - 16 - 1;
    let max = d64::MAX_EXP - 16 - 1;

    let mut group = c.benchmark_group("bid64/quantize");
    let mut data = [(0, 0); 1 << 14];
    for v in &mut data {
        let bits = random();
        let exp = thread_rng().gen_range(min..=max);
        *v = (bits, exp);
    }
    group.bench_function("rust", |b| {
        let vals = data.map(|(bits, exp)| {
            let lhs = d64::from_bits(bits);
            let rhs = d64::new(0, exp);
            (lhs, rhs)
        });
        let mut i = 0;
        b.iter(|| {
            let (lhs, rhs) = vals[i % vals.len()];
            black_box(black_box(lhs).quantize(black_box(rhs)));
            i += 1;
        });
    });
    group.bench_function("intel", |b| {
        let vals = data.map(|(bits, exp)| {
            let lhs = dfp::Bid64::from_bits(bits);
            let rhs = dfp::Bid64::new(0, exp as i32);
            (lhs, rhs)
        });
        let mut i = 0;
        b.iter(|| {
            let (lhs, rhs) = vals[i % vals.len()];
            black_box(black_box(lhs).quantize(black_box(rhs)));
            i += 1;
        });
    });
    group.finish();

    let mut group = c.benchmark_group("bid64/cmp");
    let data: [_; 1 << 14] = array::from_fn(|_| match thread_rng().gen_range(0..3) {
        0 => (random(), random()),
        1 => {
            let bits = random();
            (bits, bits)
        }
        2 => {
            let lhs = d64::from_bits(random());
            let exp = thread_rng().gen_range(min..=max);
            let rhs = lhs.quantize(d64::new(0, exp));
            (lhs.to_bits(), rhs.to_bits())
        }
        _ => unreachable!(),
    });
    group.bench_function("eq/rust", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = d64::from_bits(data[i % data.len()].0);
            let rhs = d64::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) == black_box(rhs));
            i += 1;
        });
    });
    group.bench_function("eq/intel", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = dfp::Bid64::from_bits(data[i % data.len()].0);
            let rhs = dfp::Bid64::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) == black_box(rhs));
            i += 1;
        });
    });

    group.bench_function("ge/rust", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = d64::from_bits(data[i % data.len()].0);
            let rhs = d64::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) >= black_box(rhs));
            i += 1;
        });
    });
    group.bench_function("ge/intel", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = dfp::Bid64::from_bits(data[i % data.len()].0);
            let rhs = dfp::Bid64::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) >= black_box(rhs));
            i += 1;
        });
    });

    group.bench_function("le/rust", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = d64::from_bits(data[i % data.len()].0);
            let rhs = d64::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) <= black_box(rhs));
            i += 1;
        });
    });
    group.bench_function("le/intel", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = dfp::Bid64::from_bits(data[i % data.len()].0);
            let rhs = dfp::Bid64::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) <= black_box(rhs));
            i += 1;
        });
    });
    group.finish();
}

fn bench_bid128(c: &mut Criterion) {
    let min = d128::MIN_EXP - 34 - 1;
    let max = d128::MAX_EXP - 34 - 1;

    let mut group = c.benchmark_group("bid128/quantize");
    let mut data = [(0, 0); 1 << 14];
    for v in &mut data {
        let bits = random();
        let exp = thread_rng().gen_range(min..=max);
        *v = (bits, exp);
    }
    group.bench_function("rust", |b| {
        let vals = data.map(|(bits, exp)| {
            let lhs = d128::from_bits(bits);
            let rhs = d128::new(0, exp);
            (lhs, rhs)
        });
        let mut i = 0;
        b.iter(|| {
            let (lhs, rhs) = vals[i % vals.len()];
            black_box(black_box(lhs).quantize(black_box(rhs)));
            i += 1;
        });
    });
    group.bench_function("intel", |b| {
        let vals = data.map(|(bits, exp)| {
            let lhs = dfp::Bid128::from_bits(bits);
            let rhs = dfp::Bid128::new(0, exp as i32);
            (lhs, rhs)
        });
        let mut i = 0;
        b.iter(|| {
            let (lhs, rhs) = vals[i % vals.len()];
            black_box(black_box(lhs).quantize(black_box(rhs)));
            i += 1;
        });
    });
    group.finish();

    let mut group = c.benchmark_group("bid128/cmp");
    let data: [_; 1 << 14] = array::from_fn(|_| match thread_rng().gen_range(0..3) {
        0 => (random(), random()),
        1 => {
            let bits = random();
            (bits, bits)
        }
        2 => {
            let lhs = d128::from_bits(random());
            let exp = thread_rng().gen_range(min..=max);
            let rhs = lhs.quantize(d128::new(0, exp));
            (lhs.to_bits(), rhs.to_bits())
        }
        _ => unreachable!(),
    });
    group.bench_function("eq/rust", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = d128::from_bits(data[i % data.len()].0);
            let rhs = d128::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) == black_box(rhs));
            i += 1;
        });
    });
    group.bench_function("eq/intel", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = dfp::Bid128::from_bits(data[i % data.len()].0);
            let rhs = dfp::Bid128::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) == black_box(rhs));
            i += 1;
        });
    });

    group.bench_function("ge/rust", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = d128::from_bits(data[i % data.len()].0);
            let rhs = d128::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) >= black_box(rhs));
            i += 1;
        });
    });
    group.bench_function("ge/intel", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = dfp::Bid128::from_bits(data[i % data.len()].0);
            let rhs = dfp::Bid128::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) >= black_box(rhs));
            i += 1;
        });
    });

    group.bench_function("le/rust", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = d128::from_bits(data[i % data.len()].0);
            let rhs = d128::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) <= black_box(rhs));
            i += 1;
        });
    });
    group.bench_function("le/intel", |b| {
        let mut i = 0;
        b.iter(|| {
            let lhs = dfp::Bid128::from_bits(data[i % data.len()].0);
            let rhs = dfp::Bid128::from_bits(data[i % data.len()].1);
            black_box(black_box(lhs) <= black_box(rhs));
            i += 1;
        });
    });
    group.finish();
}

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

criterion_group!(
    benches,
    bench_arith64,
    bench_arith128,
    bench_bid64,
    bench_bid128,
    bench_cmp,
    bench_div
);
criterion_main!(benches);
