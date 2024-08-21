use criterion::{black_box, criterion_group, criterion_main, Criterion};
use decnum::{bcd, dpd};
use rand::{thread_rng, Rng};

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

    let idk: Vec<u128> = (0..1024)
        .map(|_| {
            let mut bcd = 0;
            let mut rng = thread_rng();
            for _ in 0..32 {
                bcd <<= 4;
                bcd |= rng.gen_range(0..=9);
            }
            bcd
        })
        .collect();

    group.bench_function("carrying_add128_v1", |b| {
        let mut i = 0;
        let mut c = false;
        let mut sum = 0;
        b.iter(|| {
            let x = idk[i % idk.len()];
            (sum, c) = carrying_add128_v1(sum, x, c);
            i += 1;
        });
    });

    group.bench_function("carrying_add128_v2", |b| {
        let mut i = 0;
        let mut c = false;
        let mut sum = 0;
        b.iter(|| {
            let x = idk[i % idk.len()];
            (sum, c) = carrying_add128_v2(sum, x, c);
            i += 1;
        });
    });

    group.bench_function("carrying_add128_v3", |b| {
        let mut i = 0;
        let mut c = false;
        let mut sum = 0;
        b.iter(|| {
            let x = idk[i % idk.len()];
            (sum, c) = carrying_add128_v3(sum, x, c);
            i += 1;
        });
    });

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
    group.bench_function("from_bin_v1", |b| {
        let mut i = 0;
        b.iter(|| {
            let bin = bins[i % bins.len()];
            black_box(from_bin_v1(black_box(bin)));
            i += 1;
        })
    });
    group.bench_function("from_bin_v2", |b| {
        let mut i = 0;
        b.iter(|| {
            let bin = bins[i % bins.len()];
            black_box(bcd::from_bin(black_box(bin)));
            i += 1;
        })
    });

    group.finish();
}

const fn carrying_add128_v1(x: u128, mut y: u128, mut c: bool) -> (u128, bool) {
    // h/t: https://stackoverflow.com/a/78270881/2967113
    y += c as u128;
    let sum = (x ^ y) >> 1;
    let avg = (x & y) + sum + 0x33333333333333333333333333333333;
    c = (avg >> 127) != 0;
    let fixup = (sum ^ avg) & 0x88888888888888888888888888888888;
    let z = x + y + (fixup - (fixup >> 2));
    (z, c)
}

const fn carrying_add128_v2(x: u128, y: u128, mut c: bool) -> (u128, bool) {
    // h/t: https://stackoverflow.com/a/78270881/2967113
    let a = x + 0x66666666666666666666666666666666;
    let b = y + c as u128;
    let carries = (a | y) ^ ((a ^ y) & (a + b));
    c = (carries >> 127) != 0;
    let fixup = carries & 0x88888888888888888888888888888888;
    let z = (x + b) + (fixup - (fixup >> 2));
    (z, c)
}

const fn carrying_add128_v3(x: u128, y: u128, c: bool) -> (u128, bool) {
    // h/t: https://stackoverflow.com/a/78270881/2967113
    let sum = x + y + c as u128;
    let mux = (sum & !(sum + 0x66666666666666666666666666666666)) | ((x | y) & !sum);
    let c = (mux >> 127) != 0;
    let fixup = mux & 0x88888888888888888888888888888888;
    let z = sum + (fixup - (fixup >> 2));
    (z, c)
}

const fn from_bin_v1(mut bin: u16) -> u16 {
    let mut bcd = 0;
    let mut s = 0;
    while s < 16 {
        bcd |= (bin % 10) << s;
        s += 4;
        bin /= 10;
    }
    bcd
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
