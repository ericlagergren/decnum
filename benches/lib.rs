use criterion::{black_box, criterion_group, criterion_main, Criterion};
use decnum::{
    bcd::{self, Bcd16, Bcd2, Bcd32, Bcd4, Bcd8},
    u96,
};
use rand::random;

fn bench_bcd(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcd");

    group.bench_function("to_u128", |b| {
        let bcd = bcd::from_u128(random());
        b.iter(|| black_box(bcd::to_u128(black_box(bcd))))
    });
    group.bench_function("to_u64", |b| {
        let bcd = bcd::from_u64(random());
        b.iter(|| black_box(bcd::to_u64(black_box(bcd))))
    });
    group.bench_function("to_u32", |b| {
        let bcd = bcd::from_u32(random());
        b.iter(|| black_box(bcd::to_u32(black_box(bcd))))
    });
    group.bench_function("to_u16", |b| {
        let bcd = bcd::from_u16(random());
        b.iter(|| black_box(bcd::to_u16(black_box(bcd))))
    });
    group.bench_function("to_u8", |b| {
        let bcd = bcd::from_u8(random());
        b.iter(|| black_box(bcd::to_u8(black_box(bcd))))
    });

    group.bench_function("from_u128", |b| {
        let u = bcd::to_u128(random());
        b.iter(|| black_box(bcd::from_u128(black_box(u))))
    });
    group.bench_function("from_u64", |b| {
        let u = bcd::to_u64(random());
        b.iter(|| black_box(bcd::from_u64(black_box(u))))
    });
    group.bench_function("from_u32", |b| {
        let u = bcd::to_u32(random());
        b.iter(|| black_box(bcd::from_u32(black_box(u))))
    });
    group.bench_function("from_u16", |b| {
        let u = bcd::to_u16(random());
        b.iter(|| black_box(bcd::from_u16(black_box(u))))
    });
    group.bench_function("from_u8", |b| {
        let u = bcd::to_u8(random());
        b.iter(|| black_box(bcd::from_u8(black_box(u))))
    });

    group.bench_function("Bcd32::to_bin", |b| {
        let bcd = Bcd32::from_bin(random());
        b.iter(|| black_box(black_box(bcd).to_bin()))
    });
    group.bench_function("Bcd16::to_bin", |b| {
        let bcd = Bcd16::from_bin(random());
        b.iter(|| black_box(black_box(bcd).to_bin()))
    });
    group.bench_function("Bcd8::to_bin", |b| {
        let bcd = Bcd8::from_bin(random());
        b.iter(|| black_box(black_box(bcd).to_bin()))
    });
    group.bench_function("Bcd4::to_bin", |b| {
        let bcd = Bcd4::from_bin(random());
        b.iter(|| black_box(black_box(bcd).to_bin()))
    });
    group.bench_function("Bcd2::to_bin", |b| {
        let bcd = Bcd2::from_bin(random());
        b.iter(|| black_box(black_box(bcd).to_bin()))
    });

    group.bench_function("Bcd32::from_bin", |b| {
        let u = Bcd32::to_bin(&Bcd32::from_bin(random()));
        b.iter(|| black_box(Bcd32::from_bin(black_box(u))))
    });
    group.bench_function("Bcd16::from_bin", |b| {
        let u = Bcd16::to_bin(&Bcd16::from_bin(random()));
        b.iter(|| black_box(Bcd16::from_bin(black_box(u))))
    });
    group.bench_function("Bcd8::from_bin", |b| {
        let u = Bcd8::to_bin(&Bcd8::from_bin(random()));
        b.iter(|| black_box(Bcd8::from_bin(black_box(u))))
    });
    group.bench_function("Bcd4::from_bin", |b| {
        let u = Bcd4::to_bin(&Bcd4::from_bin(random()));
        b.iter(|| black_box(Bcd4::from_bin(black_box(u))))
    });
    group.bench_function("Bcd2::from_bin", |b| {
        let u = Bcd2::to_bin(&Bcd2::from_bin(random()));
        b.iter(|| black_box(Bcd2::from_bin(black_box(u))))
    });

    group.finish();
}

fn bench_overflowing_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("overflowing_mul");

    group.bench_function("u96 manual", |b| {
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(black_box(x).overflowing_mul(black_box(y))))
    });

    group.bench_function("u96 via u128", |b| {
        const fn overflowing_mul(x: u96, y: u96) -> (u96, bool) {
            const MASK: u128 = (1u128 << 96) - 1;
            const OVERFLOW: u128 = !MASK;
            let (z, c) = x.to_u128().overflowing_mul(y.to_u128());
            let overflow = c || z & OVERFLOW != 0;
            (u96::wrapping_new(z), overflow)
        }
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(overflowing_mul(black_box(x), black_box(y))))
    });

    group.finish();
}

fn bench_quorem(c: &mut Criterion) {
    let mut group = c.benchmark_group("quorem");

    group.bench_function("u96 quorem", |b| {
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(black_box(x).quorem(black_box(y))))
    });

    group.bench_function("u96 as u128", |b| {
        fn quorem(x: u96, y: u96) -> (u96, u96) {
            let q = u96::wrapping_new(x.to_u128() / y.to_u128());
            let r = u96::wrapping_new(x.to_u128() % y.to_u128());
            (q, r)
        }
        let x: u96 = random();
        let y: u96 = random();
        b.iter(|| black_box(quorem(black_box(x), black_box(y))))
    });

    group.bench_function("u96 as u128 with lt check", |b| {
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

    group.finish();
}

criterion_group!(benches, bench_bcd, bench_overflowing_mul, bench_quorem);
criterion_main!(benches);
