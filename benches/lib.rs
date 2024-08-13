use criterion::{black_box, criterion_group, criterion_main, Criterion};
use decnum::{
    bcd::{self, Bcd10, Bcd5},
    dpd,
};
use rand::{random, thread_rng, Rng};

fn bench_dpd(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpd");

    let bcds: Vec<u16> = (0..1024)
        .map(|_| bcd::from_bin(thread_rng().gen_range(0..=999)))
        .collect();
    let dpds: Vec<u16> = bcds.iter().copied().map(dpd::pack).collect();

    group.bench_function("classify", |b| {
        let mut i = 0;
        b.iter(|| {
            let dpd = dpds[i % dpds.len()];
            let _ = black_box(dpd::classify(black_box(dpd)));
            i = i.wrapping_add(1);
        })
    });

    group.bench_function("compress/pack2", |b| {
        let mut i = 0;
        b.iter(|| {
            let bcd = bcds[i % bcds.len()];
            let _ = black_box(dpd::pack_via_bits(black_box(bcd)));
            i = i.wrapping_add(1);
        })
    });
    group.bench_function("compress/pack3", |b| {
        let mut i = 0;
        b.iter(|| {
            let bcd = bcds[i % bcds.len()];
            let _ = black_box(dpd::pack_via_bits2(black_box(bcd)));
            i = i.wrapping_add(1);
        })
    });

    group.bench_function("compress/pack", |b| {
        let mut i = 0;
        b.iter(|| {
            let bcd = bcds[i % bcds.len()];
            let _ = black_box(dpd::pack(black_box(bcd)));
            i = i.wrapping_add(1);
        })
    });
    group.bench_function("expand/unpack", |b| {
        let mut i = 0;
        b.iter(|| {
            let dpd = dpds[i % bcds.len()];
            let _ = black_box(dpd::unpack(black_box(dpd)));
            i = i.wrapping_add(1);
        })
    });

    group.bench_function("compress/bcd2dpd", |b| {
        let mut i = 0;
        b.iter(|| {
            let bcd = bcds[i % bcds.len()];
            let _ = black_box(bcd2dpd(black_box(bcd)));
            i = i.wrapping_add(1);
        })
    });
    group.bench_function("expand/dpd2bcd", |b| {
        let mut i = 0;
        b.iter(|| {
            let dpd = dpds[i % bcds.len()];
            let _ = black_box(dpd2bcd(black_box(dpd)));
            i = i.wrapping_add(1);
        })
    });

    group.finish();
}

fn bench_bcd(c: &mut Criterion) {
    let mut group = c.benchmark_group("bcd");

    let bins: Vec<u16> = (0..1024).map(|_| thread_rng().gen_range(0..=999)).collect();
    let bcds: Vec<u16> = bins.iter().copied().map(bcd::from_bin).collect();

    group.bench_function("classify", |b| {
        let mut i = 0;
        b.iter(|| {
            let bcd = bcds[i % bcds.len()];
            let _ = black_box(bcd::classify(black_box(bcd)));
            i = i.wrapping_add(1);
        })
    });
    group.bench_function("to_bin", |b| {
        let mut i = 0;
        b.iter(|| {
            let bcd = bcds[i % bcds.len()];
            black_box(bcd::to_bin(black_box(bcd)));
            i += 1;
        })
    });
    group.bench_function("from_bin", |b| {
        let mut i = 0;
        b.iter(|| {
            let bin = bins[i % bins.len()];
            black_box(bcd::from_bin(black_box(bin)));
            i += 1;
        })
    });

    macro_rules! bench_to_from {
        ($ty:ty) => {{
            let bcds: Vec<$ty> = (0..8192).map(|_| <$ty>::from_bin(random())).collect();
            let bins: Vec<_> = bcds.iter().copied().map(<$ty>::to_bin).collect();

            group.bench_function(concat!(stringify!($ty), "/to_bin"), |b| {
                let mut i = 0;
                b.iter(|| {
                    let bcd = bcds[i % bcds.len()];
                    black_box(black_box(bcd).to_bin());
                    i = i.wrapping_add(1);
                })
            });
            group.bench_function(concat!(stringify!($ty), "/from_bin"), |b| {
                let mut i = 0;
                b.iter(|| {
                    let bin = bins[i % bins.len()];
                    black_box(<$ty>::from_bin(black_box(bin)));
                    i = i.wrapping_add(1);
                })
            });
            group.bench_function(concat!(stringify!($ty), "/pack"), |b| {
                let mut i = 0;
                b.iter(|| {
                    let bcd = bcds[i % bcds.len()];
                    clear();
                    black_box(bcd.pack());
                    i = i.wrapping_add(1);
                })
            });
        }};
    }
    bench_to_from!(Bcd5);
    bench_to_from!(Bcd10);

    group.finish();
}

macro_rules! bit {
    ($x:ident, $idx:literal) => {{
        (($x >> $idx) & 1) == 1
    }};
}

const fn dpd2bcd(arg: u16) -> u16 {
    let p = bit!(arg, 9);
    let q = bit!(arg, 8);
    let r = bit!(arg, 7);
    let s = bit!(arg, 6);
    let t = bit!(arg, 5);
    let u = bit!(arg, 4);
    let v = bit!(arg, 3);
    let w = bit!(arg, 2);
    let x = bit!(arg, 1);
    let y = bit!(arg, 0);

    let a = (v & w) & (!s | t | !x);
    let b = p & (!v | !w | (s & !t & x));
    let c = q & (!v | !w | (s & !t & x));
    let d = r;
    let e = v & ((!w & x) | (!t & x) | (s & x));
    let f = (s & (!v | !x)) | (p & !s & t & v & w & x);
    let g = (t & (!v | !x)) | (q & !s & t & w);
    let h = u;
    let i = v & ((!w & !x) | (w & x & (s | t)));
    let j = (!v & w) | (s & v & !w & x) | (p & w & (!x | (!s & !t)));
    let k = (!v & x) | (t & !w & x) | (q & v & w & (!x | (!s & !t)));
    let m = y;

    (m as u16)
        | ((k as u16) << 1)
        | ((j as u16) << 2)
        | ((i as u16) << 3)
        | ((h as u16) << 4)
        | ((g as u16) << 5)
        | ((f as u16) << 6)
        | ((e as u16) << 7)
        | ((d as u16) << 8)
        | ((c as u16) << 9)
        | ((b as u16) << 10)
        | ((a as u16) << 11)
}

const fn bcd2dpd(arg: u16) -> u16 {
    let a = bit!(arg, 11);
    let b = bit!(arg, 10);
    let c = bit!(arg, 9);
    let d = bit!(arg, 8);
    let e = bit!(arg, 7);
    let f = bit!(arg, 6);
    let g = bit!(arg, 5);
    let h = bit!(arg, 4);
    let i = bit!(arg, 3);
    let j = bit!(arg, 2);
    let k = bit!(arg, 1);
    let m = bit!(arg, 0);

    let p = b | (a & j) | (a & f & i);
    let q = c | (a & k) | (a & g & i);
    let r = d;
    let s = (f & (!a | !i)) | (!a & e & j) | (e & i);
    let t = g | (!a & e & k) | (a & i);
    let u = h;
    let v = a | e | i;
    let w = a | (e & i) | (!e & j);
    let x = e | (a & i) | (!a & k);
    let y = m;

    (y as u16)
        | ((x as u16) << 1)
        | ((w as u16) << 2)
        | ((v as u16) << 3)
        | ((u as u16) << 4)
        | ((t as u16) << 5)
        | ((s as u16) << 6)
        | ((r as u16) << 7)
        | ((q as u16) << 8)
        | ((p as u16) << 9)
}

fn clear() {
    // let addr: *const () = core::ptr::null();
    // unsafe {
    //     core::arch::asm!(
    //         "dc civac, {addr}",
    //         addr = in(reg) addr,
    //         options(nostack),
    //     )
    // }
}

/*
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
*/

criterion_group!(benches, bench_bcd, bench_dpd);
criterion_main!(benches);
