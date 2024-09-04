#![cfg(test)]

use std::{error, fmt};

use anyhow::{anyhow, bail, Context, Result};

use super::{conv::ParseError, ctx::RoundingMode};
use crate::{bid::Bid128, dpd::Dpd128};

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
    pub fn run<B: Backend>(&self, backend: &B) -> Result<(), Failure<'_>> {
        self.try_run(backend)
            .map_err(|err| Failure { case: self, err })
    }

    fn try_run<B: Backend>(&self, backend: &B) -> Result<(), Error> {
        match &self.op {
            Op::Apply { input, result } => {
                let got = parse_input(backend, input)?;
                self.check(backend, got, result)?;
            }
            Op::Canonical { input, result } => {
                let x = parse_input(backend, input)?;
                let got = backend.canonical(x);
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
            Op::Multiply { .. } => {
                // TODO
                // let lhs = parse_input(backend, lhs).unwrap();
                // let rhs = parse_input(backend, rhs).unwrap();
                // let got = backend.mul(lhs, rhs);
                // self.check(backend, got, result)?;
            }
            _ => return Err(Error::Unimplemented),
        };
        Ok(())
    }

    fn check<B: Backend>(&self, backend: &B, got: B::Dec, want: &str) -> Result<()> {
        if want.starts_with('#') {
            let want = backend.to_bits(parse_input(backend, want)?);
            let got = backend.to_bits(got);
            if got != want {
                Err(anyhow!("got {got:x}, expected {want:x}"))
            } else {
                Ok(())
            }
        } else {
            let got = got.to_string();
            if got != want {
                Err(anyhow!("got `{got}`, expected `{want}`"))
            } else {
                Ok(())
            }
        }
    }
}

impl fmt::Display for Test<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.id, self.op,)
    }
}

fn parse_input<B: Backend>(backend: &B, s: &str) -> Result<B::Dec> {
    if let Some(s) = s.strip_prefix('#') {
        let bytes = hex::decode(s.as_bytes())?;
        Ok(backend.from_bytes(&bytes))
    } else {
        backend.parse(s).map_err(Into::into)
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
    CopyNegate,
    CopySign,
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
    Quantize,
    Reduce,
    Remainder,
    Remaindernear,
    Rescale,
    Rotate,
    SameQuantum,
    Scaleb,
    Shift,
    SquareRoot,
    Subtract,
    ToEng,
    Tointegral,
    Tointegralx,
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
            Some((result, rest)) => (result.trim(), rest),
            None => (rest, ""),
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
            "multiply" => {
                let (lhs, rhs) = split_binop("multiply", operands)?;
                Self::Multiply { lhs, rhs, result }
            }
            _ => bail!("unknown op: `{name}`"),
        };
        Ok((op, rest))
    }
}

fn split_binop<'a>(op: &'static str, s: &'a str) -> Result<(&'a str, &'a str)> {
    let (lhs, rhs) = s
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
            _ => write!(f, "other op"),
        }
    }
}

/// A test error.
#[derive(Debug)]
pub struct Failure<'a> {
    case: &'a Test<'a>,
    err: Error,
}

impl error::Error for Failure<'_> {}

impl fmt::Display for Failure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "test failure for `{}`: {}", self.case, self.err)
    }
}

#[derive(Debug)]
enum Error {
    /// The test is unimplemented.
    Unimplemented,
    /// The test was skipped.
    Skipped,
    /// The test failed.
    Failure(anyhow::Error),
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Skipped => write!(f, "skipped"),
            Self::Unimplemented => write!(f, "unimplemented"),
            Self::Failure(err) => write!(f, "{err}"),
        }
    }
}

impl From<anyhow::Error> for Error {
    fn from(err: anyhow::Error) -> Self {
        Self::Failure(err)
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

    /// Returns the canonical form of `x` .
    fn canonical(&self, x: Self::Dec) -> Self::Dec;

    /// Compares `lhs` and `rhs`.
    fn compare(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;

    /// Returns a copy of `x`.
    fn copy(&self, x: Self::Dec) -> Self::Dec {
        x
    }

    /// Returns the absolute value of `x`.
    fn copyabs(&self, x: Self::Dec) -> Self::Dec;

    /// Multiplies `lhs * rhs`.
    fn multiply(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
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

    fn multiply(&self, lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec {
        lhs * rhs
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

macro_rules! dectest {
    ($prefix:literal, $name:literal) => {
        $crate::dectest::dectest!(::core::concat!($prefix, $name))
    };
    ($name:expr) => {{
        const CASES: &'static str =
            ::core::include_str!(::core::concat!("../../testdata/", $name, ".decTest",));
        $crate::dectest::parse(CASES).unwrap()
    }};
}
pub(crate) use dectest;

macro_rules! dectests {
    (d128) => {
        $crate::dectest::dectests!($crate::dectest::Dec128, "dq");
    };
    ($backend:ty, $prefix:literal) => {
        #[test]
        fn test_canonical() {
            for case in $crate::dectest::dectest!($prefix, "Canonical") {
                println!("case = {case}");
                case.run(&<$backend>::new()).unwrap();
                println!("");
            }
        }

        #[test]
        fn test_encode() {
            for case in $crate::dectest::dectest!($prefix, "Encode") {
                println!("case = {case}");
                case.run(&<$backend>::new()).unwrap();
                println!("");
            }
        }
    };
}
pub(crate) use dectests;
