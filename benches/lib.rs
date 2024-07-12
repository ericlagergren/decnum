use criterion::{black_box, criterion_group, criterion_main, Criterion};
use decnum::{
    bcd::{self, Bcd10, Bcd20, Bcd3, Bcd39, Bcd5},
    dpd, u96,
};
use rand::random;

fn bench_dpd(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpd");

    group.bench_function("classify_bcd", |b| {
        let bcd = bcd::from_u16(random());
        b.iter(|| black_box(dpd::classify_bcd(black_box(bcd))))
    });
    group.bench_function("classify_dpd", |b| {
        let dpd = dpd::pack(bcd::from_u16(random()));
        b.iter(|| black_box(dpd::classify_dpd(black_box(dpd))))
    });

    group.bench_function("pack all small", |b| {
        let bcd = bcd::from_u16(123);
        b.iter(|| black_box(dpd::pack(dpd::unpack(bcd))))
    });
    group.bench_function("pack all large", |b| {
        let bcd = bcd::from_u16(999);
        b.iter(|| black_box(dpd::pack(dpd::unpack(bcd))))
    });

    group.bench_function("unpack all small", |b| {
        let dpd = dpd::pack(bcd::from_u16(123));
        b.iter(|| black_box(dpd::unpack(black_box(dpd))))
    });
    group.bench_function("unpack all large", |b| {
        let dpd = dpd::pack(bcd::from_u16(999));
        b.iter(|| black_box(dpd::unpack(black_box(dpd))))
    });

    group.finish();
}

fn bench_bcd(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcd");

    macro_rules! bench_to_from_int {
        ($to:ident, $from:ident) => {
            group.bench_function(stringify!($to), |b| {
                let bcd = bcd::$from(random());
                b.iter(|| black_box(bcd::$to(black_box(bcd))))
            });
            group.bench_function(stringify!($from), |b| {
                let u = bcd::$to(random());
                b.iter(|| black_box(bcd::$from(black_box(u))))
            });
        };
    }
    bench_to_from_int!(to_u128, from_u128);
    bench_to_from_int!(to_u64, from_u64);
    bench_to_from_int!(to_u32, from_u32);
    bench_to_from_int!(to_u16, from_u16);
    bench_to_from_int!(to_u8, from_u8);

    macro_rules! bench_to_from {
        ($ty:ty) => {
            group.bench_function(concat!(stringify!($ty, "::to_bin")), |b| {
                let bcd = <$ty>::from_bin(random());
                b.iter(|| black_box(black_box(bcd).to_bin()))
            });
            group.bench_function(concat!(stringify!($ty, "::from_bin")), |b| {
                let u = <$ty>::to_bin(&<$ty>::from_bin(random()));
                b.iter(|| black_box(<$ty>::from_bin(black_box(u))))
            });
        };
    }
    bench_to_from!(Bcd39);
    bench_to_from!(Bcd20);
    bench_to_from!(Bcd10);
    bench_to_from!(Bcd5);
    bench_to_from!(Bcd3);

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

criterion_group!(
    benches,
    bench_bcd,
    bench_dpd,
    bench_overflowing_mul,
    bench_quorem
);
criterion_main!(benches);
