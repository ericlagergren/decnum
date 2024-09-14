//! Partially borrowed from [`rust-dec`].
//!
//! [`rust-dec`]: https://github.com/MaterializeInc/rust-dec/tree/e33480a6915c4767c9e56e3c5d1394b0b89e5fbe/dectest

#![cfg(test)]

mod op;
mod parse;
use std::{error, fmt};

use anyhow::{anyhow, Result};
use op::Op;
pub use parse::parse;

use super::{conv::ParseError, ctx::RoundingMode};
use crate::{bid::Bid128, dpd::Dpd128};

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
    pub rounding: RoundingMode,
    pub id: &'a str,
    pub op: Op<'a>,
    pub result: &'a str,
}

impl Test<'_> {
    /// Runs a test.
    pub fn run<B: Backend>(&self, backend: &B) -> Result<(), Error> {
        let result = self.result;
        match &self.op {
            Op::Add { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.subtract(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            Op::Apply { input } => {
                let got = parse_input(backend, input)?;
                self.check(backend, got, result)?;
            }
            Op::Canonical { input } => {
                let x = parse_input(backend, input)?;
                let got = backend.canonical(x);
                self.check(backend, got, result)?;
            }
            Op::Compare { lhs, rhs } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.compare(lhs, rhs);
                self.check(backend, got, result)?;
            }
            Op::CompareTotal { lhs, rhs } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.comparetotal(lhs, rhs);
                self.check(backend, got, result)?;
            }
            Op::Copy { input } => {
                let x = parse_input(backend, input)?;
                let got = backend.copy(x);
                self.check(backend, got, result)?;
            }
            Op::CopyAbs { input } => {
                let x = parse_input(backend, input)?;
                let got = backend.copyabs(x);
                self.check(backend, got, result)?;
            }
            Op::CopyNegate { input } => {
                let x = parse_input(backend, input)?;
                let got = backend.copynegate(x);
                self.check(backend, got, result)?;
            }
            Op::CopySign { lhs, rhs } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.copysign(lhs, rhs);
                self.check(backend, got, result)?;
            }
            Op::Max { lhs, rhs } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.max(lhs, rhs);
                self.check(backend, got, result)?;
            }
            Op::Min { lhs, rhs } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.min(lhs, rhs);
                self.check(backend, got, result)?;
            }
            Op::Multiply { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.multiply(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            Op::Subtract { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.subtract(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            Op::ToIntegralX { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.tointegralx(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            Op::Quantize { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.quantize(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            _ => return Err(Error::Unimplemented),
        };
        Ok(())
    }

    fn check<B: Backend>(&self, backend: &B, got: B::Dec, want: &str) -> Result<(), Error> {
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

        let got = got.to_string();
        if got != want {
            failure!("got `\"{got}\"`, expected `\"{want}\"`")
        } else {
            Ok(())
        }
    }
}

fn parse_input<B: Backend>(backend: &B, s: &str) -> Result<B::Dec, Error> {
    let s = s.strip_prefix('\'').unwrap_or(s);
    let s = s.strip_suffix('\'').unwrap_or(s);

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
        write!(f, "{} {}", self.id, self.op,)
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

    fn canonical(&self, x: Self::Dec) -> Self::Dec;
    fn compare(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn comparetotal(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn copy(&self, x: Self::Dec) -> Self::Dec {
        x
    }
    fn copyabs(&self, x: Self::Dec) -> Self::Dec;
    fn copynegate(&self, x: Self::Dec) -> Self::Dec;
    fn copysign(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn max(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn min(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn multiply(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn quantize(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn subtract(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
    fn tointegralx(&self, x: Self::Dec) -> Self::Dec;
}

/// A backend for [`Bid128`] and [`Dpd128`].
pub struct Dec128;

impl Dec128 {
    /// Creates a [`Dec128`].
    pub const fn new() -> Self {
        Self
    }
}

impl Backend for Dec128 {
    type Dec = Bid128;
    type Bits = u128;

    fn to_bits(&self, dec: Self::Dec) -> Self::Bits {
        dec.to_dpd128().to_bits()
    }

    fn from_bytes(&self, bytes: &[u8]) -> Self::Dec {
        println!("bytes = {}", bytes.len());
        Dpd128::from_be_bytes(bytes.try_into().unwrap()).to_bid128()
    }

    fn parse(&self, s: &str) -> Result<Self::Dec, ParseError> {
        Bid128::parse(s)
    }

    fn canonical(&self, x: Self::Dec) -> Self::Dec {
        x.canonical()
    }

    fn compare(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs.compare(rhs)
    }

    fn comparetotal(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs.compare_total(rhs)
    }

    fn copyabs(&self, x: Self::Dec) -> Self::Dec {
        x.abs()
    }

    fn copynegate(&self, x: Self::Dec) -> Self::Dec {
        x.const_neg()
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

    fn multiply(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs * rhs
    }

    fn quantize(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs.quantize(rhs)
    }

    fn subtract(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs - rhs
    }

    fn tointegralx(&self, x: Self::Dec) -> Self::Dec {
        x.round_to_integral_exact()
    }
}

/// An integer like `u32`, `u128`, etc.
pub trait Bits: Copy + Eq + PartialEq + fmt::Debug + fmt::LowerHex + Sized {
    /// Parses itself from bytes.
    fn from_bytes(bytes: &[u8]) -> Result<Self>;
}
impl Bits for u32 {
    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(Self::from_le_bytes(bytes.try_into()?))
    }
}
impl Bits for u64 {
    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(Self::from_le_bytes(bytes.try_into()?))
    }
}
impl Bits for u128 {
    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(Self::from_le_bytes(bytes.try_into()?))
    }
}

macro_rules! dectests {
    (d128) => {
        $crate::dectest::dectests!($crate::dectest::Dec128, "dq");
    };
    ($backend:ty, $prefix:literal) => {
        $crate::dectest::dectests!($backend, $prefix,
            test_canonical => "Canonical",
            test_compare => "Compare",
            test_compare_total => "CompareTotal",
            test_encode => "Encode",
            test_max => "Max",
            test_min => "Min",
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
                    match case.run(&<$backend>::new()) {
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
