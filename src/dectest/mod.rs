#![cfg(test)]

use std::{error, fmt};

use anyhow::{anyhow, bail, Context, Result};

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

/// Parses test cases.
pub fn parse(s: &str) -> Result<Vec<Test<'_>>> {
    let mut extended = 1;
    let mut precision: u32 = 0;
    let mut max_exp: i16 = 0;
    let mut min_exp: i16 = 0;
    let mut rounding: RoundingMode = RoundingMode::default();
    let mut clamp = 0;
    let mut cases = Vec::new();
    for (i, line) in s.lines().enumerate() {
        if line.is_empty() {
            continue;
        }

        if line.starts_with("--") {
            // A comment.
            continue;
        }

        if let Some((_, _)) = line.split_once("version: ") {
            continue;
        }

        if let Some((_, v)) = line.split_once("precision: ") {
            precision = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse precision: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("rounding: ") {
            rounding = RoundingMode::try_from_str(v.trim())
                .with_context(|| format!("#{i}: invalid rounding mode: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("maxExponent: ") {
            max_exp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `maxExponent`: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("minExponent: ") {
            min_exp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `minExponent`: `{v}`"))?;
            continue;
        }
        if let Some((_, v)) = line.split_once("minexponent: ") {
            min_exp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `minexponent`: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("extended: ") {
            extended = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `extended`: `{v}`"))?;
            continue;
        }

        if let Some((_, v)) = line.split_once("clamp: ") {
            clamp = v
                .trim()
                .parse()
                .with_context(|| format!("#{i}: unable to parse `clamp`: `{v}`"))?;
            continue;
        }

        //println!("line = {line}");
        let (name, rest) = line
            .split_once(" ")
            .with_context(|| format!("#{i}: test case missing name: `{line}`"))?;
        let (op, rest) = Op::parse(rest.trim())
            .with_context(|| format!("#{i}: unable to parse op: `{rest}`"))?;
        let _ = rest; // TODO: conds
        let case = Test {
            extended: extended == 1,
            clamp: clamp == 1,
            precision,
            max_exp,
            min_exp,
            rounding,
            id: name,
            op,
        };
        cases.push(case);
    }
    assert!(!cases.is_empty());
    Ok(cases)
}

/// A specific test case.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Test<'a> {
    pub extended: bool,
    pub clamp: bool,
    pub precision: u32,
    pub max_exp: i16,
    pub min_exp: i16,
    pub rounding: RoundingMode,
    pub id: &'a str,
    pub op: Op<'a>,
}

impl Test<'_> {
    /// Runs a test.
    pub fn run<B: Backend>(&self, backend: &B) -> Result<(), Error> {
        match &self.op {
            Op::Add { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.subtract(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            Op::Apply { input, result } => {
                let got = parse_input(backend, input)?;
                self.check(backend, got, result)?;
            }
            Op::Canonical { input, result } => {
                let x = parse_input(backend, input)?;
                let got = backend.canonical(x);
                self.check(backend, got, result)?;
            }
            Op::Compare { lhs, rhs, result } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.compare(lhs, rhs);
                self.check(backend, got, result)?;
            }
            Op::Copy { input, result } => {
                let x = parse_input(backend, input)?;
                let got = backend.copy(x);
                self.check(backend, got, result)?;
            }
            Op::CopyAbs { input, result } => {
                let x = parse_input(backend, input)?;
                let got = backend.copyabs(x);
                self.check(backend, got, result)?;
            }
            Op::CopyNegate { input, result } => {
                let x = parse_input(backend, input)?;
                let got = backend.copynegate(x);
                self.check(backend, got, result)?;
            }
            Op::CopySign { lhs, rhs, result } => {
                let lhs = parse_input(backend, lhs)?;
                let rhs = parse_input(backend, rhs)?;
                let got = backend.copysign(lhs, rhs);
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

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op<'a> {
    Abs {
        input: &'a str,
        result: &'a str,
    },
    Add {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    And,
    Apply {
        input: &'a str,
        result: &'a str,
    },
    Canonical {
        input: &'a str,
        result: &'a str,
    },
    Class,
    Compare {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    CompareSig {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    CompareTotal,
    CompareTotMag,
    Copy {
        input: &'a str,
        result: &'a str,
    },
    CopyAbs {
        input: &'a str,
        result: &'a str,
    },
    CopyNegate {
        input: &'a str,
        result: &'a str,
    },
    CopySign {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    Divide,
    DivideInt,
    Exp,
    Fma,
    Invert,
    Ln,
    Log10,
    Logb,
    Max,
    Min,
    MaxMag,
    MinMag,
    Minus,
    Multiply {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    NextMinus,
    NextPlus,
    NextToward,
    Or,
    Plus,
    Power,
    Quantize {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    Reduce,
    Remainder,
    Remaindernear,
    Rescale,
    Rotate,
    SameQuantum,
    Scaleb,
    Shift,
    SquareRoot,
    Subtract {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    ToEng,
    ToIntegral,
    ToIntegralX {
        input: &'a str,
        result: &'a str,
    },
    ToSci,
    Trim,
    Xor,
}

impl<'a> Op<'a> {
    fn parse(s: &'a str) -> Result<(Self, &'a str)> {
        let (name, rest) = s
            .split_once(' ')
            .with_context(|| "unable to parse op name")?;
        let (operands, rest) = rest
            .split_once("->")
            .with_context(|| "unable to split on `->`")?;
        let (result, rest) = match rest.trim().split_once(' ') {
            Some((result, rest)) => (result.trim(), rest.trim()),
            None => (rest.trim(), ""),
        };
        let op = match name {
            "abs" => Self::Abs {
                input: operands.trim(),
                result,
            },
            "add" => {
                let (lhs, rhs) = split_binop("add", operands)?;
                Self::Add { lhs, rhs, result }
            }
            "apply" => Self::Apply {
                input: operands.trim(),
                result,
            },
            "canonical" => Self::Canonical {
                input: operands.trim(),
                result,
            },
            "compare" => {
                let (lhs, rhs) = split_binop("compare", operands)?;
                Self::Compare { lhs, rhs, result }
            }
            "comparesig" => {
                let (lhs, rhs) = split_binop("comparesig", operands)?;
                Self::Compare { lhs, rhs, result }
            }
            "copy" => Self::Copy {
                input: operands.trim(),
                result,
            },
            "copyabs" => Self::CopyAbs {
                input: operands.trim(),
                result,
            },
            "copynegate" => Self::CopyNegate {
                input: operands.trim(),
                result,
            },
            "copysign" => {
                let (lhs, rhs) = split_binop("copysign", operands)?;
                Self::CopySign { lhs, rhs, result }
            }
            "multiply" => {
                let (lhs, rhs) = split_binop("multiply", operands)?;
                Self::Multiply { lhs, rhs, result }
            }
            "quantize" => {
                let (lhs, rhs) = split_binop("quantize", operands)?;
                Self::Quantize { lhs, rhs, result }
            }
            "subtract" => {
                let (lhs, rhs) = split_binop("subtract", operands)?;
                Self::Subtract { lhs, rhs, result }
            }
            "tointegralx" => Self::ToIntegralX {
                input: operands.trim(),
                result,
            },
            _ => bail!("unknown op: `{name}`"),
        };
        Ok((op, rest))
    }
}

fn split_binop<'a>(op: &'static str, s: &'a str) -> Result<(&'a str, &'a str)> {
    let (lhs, rhs) = s
        .trim()
        .split_once(" ")
        .with_context(|| format!("unable to parse `{op}` operands"))?;
    Ok((lhs.trim(), rhs.trim()))
}

impl fmt::Display for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Abs { input, result } => {
                write!(f, "abs {input} -> {result}")
            }
            Self::Add { lhs, rhs, result } => {
                write!(f, "add {lhs} {rhs} -> {result}")
            }
            Self::Apply { input, result } => {
                write!(f, "apply {input} -> {result}")
            }
            Self::Canonical { input, result } => {
                write!(f, "canonical {input} -> {result}")
            }
            Self::Compare { lhs, rhs, result } => {
                write!(f, "compare {lhs} {rhs} -> {result}")
            }
            Self::CompareSig { lhs, rhs, result } => {
                write!(f, "comparesig {lhs} {rhs} -> {result}")
            }
            Self::Copy { input, result } => {
                write!(f, "copy {input} -> {result}")
            }
            Self::CopyAbs { input, result } => {
                write!(f, "copyabs {input} -> {result}")
            }
            Self::CopyNegate { input, result } => {
                write!(f, "copynegate {input} -> {result}")
            }
            Self::CopySign { lhs, rhs, result } => {
                write!(f, "copysign {lhs} {rhs} -> {result}")
            }
            Self::Quantize { lhs, rhs, result } => {
                write!(f, "quantize {lhs} {rhs} -> {result}")
            }
            Self::Subtract { lhs, rhs, result } => {
                write!(f, "subtract {lhs} {rhs} -> {result}")
            }
            Self::ToIntegralX { input, result } => {
                write!(f, "tointegralx {input} -> {result}")
            }
            _ => write!(f, "other op"),
        }
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
    fn copy(&self, x: Self::Dec) -> Self::Dec {
        x
    }
    fn copyabs(&self, x: Self::Dec) -> Self::Dec;
    fn copynegate(&self, x: Self::Dec) -> Self::Dec;
    fn copysign(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
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

    fn copyabs(&self, x: Self::Dec) -> Self::Dec {
        x.abs()
    }

    fn copynegate(&self, x: Self::Dec) -> Self::Dec {
        x.const_neg()
    }

    fn copysign(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs.copy_sign(rhs)
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
            test_encode => "Encode",
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
