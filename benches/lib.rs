use criterion::{black_box, criterion_group, criterion_main, Criterion};
use decnum::u96;
use rand::random;

fn bench_quorem(c: &mut Criterion) {
    c.bench_function("quorem", |b| {
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(black_box(x).quorem(black_box(y))))
    });

    c.bench_function("quorem_u128", |b| {
        fn quorem(x: u96, y: u96) -> (u96, u96) {
            let q = u96::wrapping_new(x.to_u128() / y.to_u128());
            let r = u96::wrapping_new(x.to_u128() % y.to_u128());
            (q, r)
        }
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(quorem(black_box(x), black_box(y))))
    });

    c.bench_function("quorem_u128_check", |b| {
        fn quorem(x: u96, y: u96) -> (u96, u96) {
            if x < y {
                return (u96::MIN, x);
            }
            if let Some(y) = y.try_to_u64() {
                let (q, r) = x.quorem64(y);
                return (q, u96::from_u64(r));
            }
            let q = u96::wrapping_new(x.to_u128() / y.to_u128());
            let r = u96::wrapping_new(x.to_u128() % y.to_u128());
            (q, r)
        }
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(quorem(black_box(x), black_box(y))))
    });
}

criterion_group!(benches, bench_quorem);
criterion_main!(benches);
