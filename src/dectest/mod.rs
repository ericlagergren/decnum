//! Partially borrowed from [`rust-dec`].
//!
//! [`rust-dec`]: https://github.com/MaterializeInc/rust-dec/tree/e33480a6915c4767c9e56e3c5d1394b0b89e5fbe/dectest

#![cfg(test)]
#![allow(dead_code)] // TODO

mod op;
mod parse;
use std::{error, fmt};

use anyhow::{anyhow, Result};
use op::Op;
pub use parse::parse;

use super::{
    conv::ParseError,
    ctx::{Ctx, RoundingMode},
};

macro_rules! failure {
    ($msg:literal $(,)?) => {
        Err(anyhow!($msg).into())
    };
    ($err:expr $(,)?) => {
        Err(anyhow!($err).into())
    };
    ($fmt:expr, $($arg:tt)*) => {
        Err(anyhow!($fmt, $($arg)*).into())
    };
}

/// A specific test case.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Test<'a> {
    pub extended: bool,
    pub clamp: bool,
    pub precision: i32,
    pub max_exp: i32,
    pub min_exp: i32,
    pub rounding: &'a str,
    pub id: &'a str,
    pub op: Op<'a>,
    pub result: &'a str,
}

impl Test<'_> {
    /// Runs a test.
    pub fn run<B: Backend>(&self, backend: &mut B) -> Result<(), Error> {
        macro_rules! unary {
            (@str $input:expr, $f:ident) => {
                match $input {
                    input => {
                        let input = parse_input(backend, input)?;
                        let got = backend.$f(input);
                        Self::check_str(got, self.result)?;
                    }
                }
            };
            ($input:expr, $f:ident) => {
                match $input {
                    input => {
                        let input = parse_input(backend, input)?;
                        let got = backend.$f(input);
                        Self::check(backend, got, self.result)?;
                    }
                }
            };
        }

        macro_rules! binary {
            (@bool ($lhs:expr, $rhs:expr), $f:ident) => {
                match ($lhs, $rhs) {
                    (lhs, rhs) => {
                        let lhs = parse_input(backend, lhs)?;
                        let rhs = parse_input(backend, rhs)?;
                        let got = backend.$f(lhs, rhs);
                        Self::check_bool(got, self.result)?;
                    }
                }
            };
            (($lhs:expr, $rhs:expr), $f:ident) => {
                match ($lhs, $rhs) {
                    (lhs, rhs) => {
                        let lhs = parse_input(backend, lhs)?;
                        let rhs = parse_input(backend, rhs)?;
                        let got = backend.$f(lhs, rhs);
                        Self::check(backend, got, self.result)?;
                    }
                }
            };
        }

        use RoundingMode::*;
        let mode = match self.rounding {
            "ceiling" => ToPositiveInf,
            "down" => ToZero,
            "floor" => ToNegativeInf,
            "half_down" => ToNearestTowardZero,
            "half_even" => ToNearestEven,
            "half_up" => ToNearestAway,
            "up" => AwayFromZero,
            "05up" => return Err(Error::Unsupported),
            s => return Err(anyhow!("unknown rounding mode: {s}").into()),
        };
        backend.set_rounding_mode(mode);

        use Op::*;
        match &self.op {
            Abs { input } => unary!(input, abs),
            Add { lhs, rhs } => binary!((lhs, rhs), add),
            Apply { input } => {
                let got = parse_input(backend, input)?;
                Self::check(backend, got, self.result)?;
            }
            Canonical { input } => unary!(input, canonical),
            Class { input } => unary!(@str input, class),
            Compare { lhs, rhs } => binary!((lhs, rhs), compare),
            CompareSig { lhs, rhs } => binary!((lhs, rhs), comparesig),
            CompareTotal { lhs, rhs } => binary!((lhs, rhs), comparetotal),
            Copy { input } => unary!(input, copy),
            CopyAbs { input } => unary!(input, copyabs),
            CopyNegate { input } => unary!(input, copynegate),
            CopySign { lhs, rhs } => binary!((lhs, rhs), copysign),
            Max { lhs, rhs } => binary!((lhs, rhs), max),
            Min { lhs, rhs } => binary!((lhs, rhs), min),
            MaxMag { lhs, rhs } => binary!((lhs, rhs), maxmag),
            MinMag { lhs, rhs } => binary!((lhs, rhs), minmag),
            Minus { input } => unary!(input, minus),
            Multiply { .. } => {
                // binary!((lhs, rhs), multiply)
            }
            NextMinus { input } => unary!(input, nextminus),
            NextPlus { input } => unary!(input, nextplus),
            Plus { input } => unary!(input, plus),
            SameQuantum { lhs, rhs } => binary!(@bool (lhs, rhs), samequantum),
            Subtract { .. } => {
                //binary!((lhs, rhs), subtract)
            }
            ToIntegralX { .. } => {
                // unary!(...)
            }
            Quantize { lhs, rhs } => binary!((lhs, rhs), quantize),
            _ => return Err(Error::Unimplemented),
        };
        Ok(())
    }

    fn check<B: Backend>(backend: &B, got: B::Dec, want: &str) -> Result<(), Error> {
        if want == "#" {
            return Err(Error::Unsupported);
        }

        if want.starts_with('#') {
            let want = backend.to_bits(parse_input(backend, want)?);
            let got = backend.to_bits(got);
            return if got != want {
                failure!("got `{got:x}`, expected `{want:x}`")
            } else {
                Ok(())
            };
        }

        Self::check_str(&got.to_string(), want)
    }

    fn check_bool(got: bool, want: &str) -> Result<(), Error> {
        debug_assert!(want == "0" || want == "1");

        let want = want == "1";
        if got != want {
            failure!("got `\"{got}\"`, expected `\"{want}\"`")
        } else {
            Ok(())
        }
    }

    fn check_str(got: &str, want: &str) -> Result<(), Error> {
        if got != want {
            failure!("got `\"{got}\"`, expected `\"{want}\"`")
        } else {
            Ok(())
        }
    }
}

fn parse_input<B: Backend>(backend: &B, s: &str) -> Result<B::Dec, Error> {
    if s == "#" {
        Err(Error::Unsupported)
    } else if let Some(s) = s.strip_prefix('#') {
        let bytes = hex::decode(s.as_bytes()).map_err(|err| Error::Failure(Box::new(err)))?;
        Ok(backend.from_bytes(&bytes))
    } else {
        backend
            .parse(s)
            .map_err(|err| Error::Failure(Box::new(err)))
    }
}

impl fmt::Display for Test<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} -> {} ({:?})",
            self.id, self.op, self.result, self.rounding
        )
    }
}

/// A test error.
#[derive(Debug)]
pub enum Error {
    /// The test failed.
    Failure(Box<dyn error::Error>),
    /// The test was skipped.
    Skipped,
    /// The test is unimplemented.
    Unimplemented,
    /// The test is unsupported.
    Unsupported,
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Failure(err) => write!(f, "{err}"),
            Self::Skipped => write!(f, "skipped"),
            Self::Unimplemented => write!(f, "unimplemented"),
            Self::Unsupported => write!(f, "unsupported"),
        }
    }
}

impl From<anyhow::Error> for Error {
    fn from(err: anyhow::Error) -> Self {
        Self::Failure(err.into())
    }
}

/// A testing backend.
pub trait Backend {
    /// The underlying decimal.
    type Dec: Copy + fmt::Display + Sized;
    /// The decimal's bit representation.
    type Bits: Bits;

    /// Creates a decimal from bytes.
    fn from_bytes(&self, bytes: &[u8]) -> Self::Dec;

    /// Parses a decimal from a string.
    fn parse(&self, s: &str) -> Result<Self::Dec, ParseError>;

    /// Converts the decimal to its bit representation.
    fn to_bits(&self, dec: Self::Dec) -> Self::Bits;

    fn set_rounding_mode(&mut self, mode: RoundingMode);

    fn abs(&self, x: Self::Dec) -> Self::Dec;
    fn add(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn canonical(&self, x: Self::Dec) -> Self::Dec;
    fn class(&self, x: Self::Dec) -> &'static str;
    fn compare(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn comparesig(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn comparetotal(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn copy(&self, x: Self::Dec) -> Self::Dec;
    fn copyabs(&self, x: Self::Dec) -> Self::Dec;
    fn copynegate(&self, x: Self::Dec) -> Self::Dec;
    fn copysign(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn max(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn min(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn maxmag(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn minmag(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn minus(&self, x: Self::Dec) -> Self::Dec;
    fn multiply(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn nextminus(&self, x: Self::Dec) -> Self::Dec;
    fn nextplus(&self, x: Self::Dec) -> Self::Dec;
    fn plus(&self, x: Self::Dec) -> Self::Dec;
    fn quantize(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn samequantum(&self, lhs: Self::Dec, rhs: Self::Dec) -> bool;
    fn subtract(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn tointegralx(&self, x: Self::Dec) -> Self::Dec;
}

macro_rules! impl_backend {
    ($dec:ty, $dpd:ty, $bits:ty) => {
        impl $crate::dectest::Backend for $crate::dectest::Default<$dec> {
            type Dec = $dec;
            type Bits = $bits;

            fn to_bits(&self, dec: Self::Dec) -> Self::Bits {
                dec.to_dpd().to_bits()
            }

            fn from_bytes(&self, bytes: &[u8]) -> Self::Dec {
                <$dpd>::from_be_bytes(bytes.try_into().unwrap()).to_bid()
            }

            fn parse(&self, s: &str) -> Result<Self::Dec, $crate::conv::ParseError> {
                <$dec>::parse(s)
            }

            fn set_rounding_mode(&mut self, mode: $crate::ctx::RoundingMode) {
                self.ctx = self.ctx.with_rounding_mode(mode);
            }

            fn abs(&self, x: Self::Dec) -> Self::Dec {
                x.abs()
            }

            fn add(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                self.ctx.const_add(lhs, rhs)
            }

            fn canonical(&self, x: Self::Dec) -> Self::Dec {
                x.canonical()
            }

            fn class(&self, x: Self::Dec) -> &'static str {
                x.class()
            }

            fn compare(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.compare(rhs)
            }

            fn comparesig(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.compare_sig(rhs)
            }

            fn comparetotal(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.compare_total(rhs)
            }

            fn copy(&self, x: Self::Dec) -> Self::Dec {
                x
            }

            fn copyabs(&self, x: Self::Dec) -> Self::Dec {
                x.copy_abs()
            }

            fn copynegate(&self, x: Self::Dec) -> Self::Dec {
                x.copy_neg()
            }

            fn copysign(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.copy_sign(rhs)
            }

            fn max(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.max(rhs)
            }

            fn min(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.min(rhs)
            }

            fn maxmag(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.max_mag(rhs)
            }

            fn minmag(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                lhs.min_mag(rhs)
            }

            fn minus(&self, x: Self::Dec) -> Self::Dec {
                -x
            }

            fn multiply(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                self.ctx.const_mul(lhs, rhs)
            }

            fn nextminus(&self, x: Self::Dec) -> Self::Dec {
                self.ctx.next_down(x)
            }

            fn nextplus(&self, x: Self::Dec) -> Self::Dec {
                self.ctx.next_up(x)
            }

            fn plus(&self, x: Self::Dec) -> Self::Dec {
                x.plus()
            }

            fn quantize(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                self.ctx.quantize(lhs, rhs)
            }

            fn samequantum(&self, lhs: Self::Dec, rhs: Self::Dec) -> bool {
                lhs.same_quantum(rhs)
            }

            fn subtract(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
                self.ctx.const_sub(lhs, rhs)
            }

            fn tointegralx(&self, x: Self::Dec) -> Self::Dec {
                self.ctx.round_to_integral_exact(x)
            }
        }
    };
}
pub(crate) use impl_backend;

/// A default backend for [`Bid128`], [`Bid64`], etc.
pub struct Default<T> {
    pub(crate) ctx: Ctx<T>,
}

impl<T> Default<T> {
    /// Creates a new backend.
    pub const fn new() -> Self {
        Self { ctx: Ctx::new() }
    }
}

/// An integer like `u32`, `u128`, etc.
pub trait Bits: Copy + Eq + PartialEq + fmt::Debug + fmt::LowerHex + Sized {}

macro_rules! impl_bits {
    ($($ty:ty),*) => {
        $(
            impl Bits for $ty {}
        )*
    }
}
impl_bits!(u32, u64, u128);

macro_rules! dectests {
    (d32 $backend:ty, $prefix:literal) => {
        $crate::dectest::dectests!($backend, $prefix,
            test_base => "Base",
            test_encode => "Encode",
        );
    };
    (d64 $backend:ty, $prefix:literal) => {
        $crate::dectest::dectests!(d128 $backend, $prefix);
    };
    (d128 $backend:ty, $prefix:literal) => {
        $crate::dectest::dectests!($backend, $prefix,
            test_abs => "Abs",
            test_add => "Add",
            test_canonical => "Canonical",
            test_class => "Class",
            test_compare => "Compare",
            test_compare_total => "CompareTotal",
            test_copy => "Copy",
            test_copy_abs => "CopyAbs",
            test_copy_neg => "CopyNegate",
            test_encode => "Encode",
            test_max => "Max",
            test_max_mag => "MaxMag",
            test_min => "Min",
            test_min_mag => "MinMag",
            test_minus => "Minus",
            test_next_down => "NextMinus",
            test_next_up => "NextPlus",
            test_plus => "Plus",
            test_quantize => "Quantize",
            test_same_quantum => "SameQuantum",
            test_sub => "Subtract",
        );
    };
    ($backend:ty, $prefix:literal, $($name:ident => $test:expr),+ $(,)?) => {
        $(
            #[test]
            fn $name() {
                const CASES: &'static str = ::core::include_str!(
                    ::core::concat!("../../testdata/", $prefix, $test, ".decTest"),
                );
                for case in $crate::dectest::parse(CASES).unwrap() {
                    println!("case = {case}");
                    match case.run(&mut <$backend>::new()) {
                        Err($crate::dectest::Error::Unsupported) => continue,
                        v => v.unwrap(),
                    }
                    println!("");
                }
            }
        )+
    };
}
pub(crate) use dectests;
