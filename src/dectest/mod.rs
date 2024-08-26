#![cfg(test)]

use std::{error, fmt};

use anyhow::{anyhow, bail, Context, Result};

use super::{conv::ParseError, ctx::RoundingMode};
use crate::{bid::Bid128, dpd::Dpd128};

pub fn parse(s: &str) -> Result<Vec<Case<'_>>> {
    let mut extended = 0;
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

        println!("line = {line}");
        let (name, rest) = line
            .split_once(" ")
            .with_context(|| format!("#{i}: test case missing name: `{line}`"))?;
        let case = Case {
            extended: extended == 1,
            clamp: clamp == 1,
            precision,
            max_exp,
            min_exp,
            rounding,
            name,
            op: Op::parse(rest.trim())
                .with_context(|| format!("#{i}: unable to parse op: `{rest}`"))?,
        };
        cases.push(case);
    }
    assert!(!cases.is_empty());
    Ok(cases)
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Case<'a> {
    pub extended: bool,
    pub clamp: bool,
    pub precision: u32,
    pub max_exp: i16,
    pub min_exp: i16,
    pub rounding: RoundingMode,
    pub name: &'a str,
    pub op: Op<'a>,
}

impl Case<'_> {
    pub fn run<B: Backend>(&self) -> Result<(), Failure<'_>> {
        self.try_run::<B>()
            .map_err(|err| Failure { case: self, err })
    }

    fn try_run<B: Backend>(&self) -> Result<()> {
        match &self.op {
            Op::Apply { input, output } => {
                let got = parse_input::<B>(input)?;
                self.check(got, output)
            }
            Op::Multiply { lhs, rhs, output } => {
                let lhs = parse_input::<B>(lhs).unwrap();
                let rhs = parse_input::<B>(rhs).unwrap();
                let got = B::mul(lhs, rhs);
                self.check(got, output)
            }
            _ => Ok(()),
        }
    }

    fn check<G>(&self, got: G, want: &str) -> Result<()>
    where
        G: fmt::Display,
    {
        let got = got.to_string();
        if got != want {
            Err(anyhow!("got {got}, expected {want}"))
        } else {
            Ok(())
        }
    }
}

impl fmt::Display for Case<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name, self.op,)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op<'a> {
    Abs {
        input: &'a str,
        output: &'a str,
    },
    Add,
    And,
    Apply {
        input: &'a str,
        output: &'a str,
    },
    Canonical,
    Class,
    Compare,
    CompareSig,
    CompareTotal,
    CompareTotMag,
    Copy,
    CopyAbs,
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
        output: &'a str,
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
    fn parse(s: &'a str) -> Result<Self> {
        println!("parse op `{s}`");
        let (name, s) = s
            .split_once(" ")
            .with_context(|| "unable to split op name")?;
        let op = match name {
            "abs" => {
                let (input, output) = s
                    .split_once("->")
                    .with_context(|| "unable to parse `abs`")?;
                Self::Abs {
                    input: input.trim(),
                    output: output.trim(),
                }
            }
            "apply" => {
                let (input, output) = s
                    .split_once("->")
                    .with_context(|| "unable to parse `apply`")?;
                Self::Apply {
                    input: input.trim(),
                    output: output.trim(),
                }
            }
            "multiply" => {
                let (lhs, rest) = s
                    .split_once(" ")
                    .with_context(|| "unable to parse `multiply`")?;
                let (rhs, output) = rest
                    .split_once("->")
                    .with_context(|| "unable to parse `abs`")?;
                Self::Multiply {
                    lhs: lhs.trim(),
                    rhs: rhs.trim(),
                    output: output.trim(),
                }
            }
            _ => bail!("unknown op: `{name}`"),
        };
        Ok(op)
    }
}

impl fmt::Display for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Apply { input, output } => {
                write!(f, "apply {input} -> {output}")
            }
            _ => write!(f, "other op"),
        }
    }
}

fn parse_input<B: Backend>(s: &str) -> Result<B::Dec> {
    if let Some(s) = s.strip_prefix('#') {
        let bytes = hex::decode(s.as_bytes())?;
        let bits = Bits::from_bytes(&bytes)?;
        Ok(B::from_bits(bits))
    } else {
        B::parse(s).map_err(Into::into)
    }
}

#[derive(Debug)]
pub enum Error<'a> {
    Unimplemented,
    Skipped,
    Failure(Failure<'a>),
}

impl error::Error for Error<'_> {}

impl fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Skipped => write!(f, "skipped"),
            Self::Unimplemented => write!(f, "unimplemented"),
            Self::Failure(err) => write!(f, "{err}"),
        }
    }
}

impl<'a> From<Failure<'a>> for Error<'a> {
    fn from(err: Failure<'a>) -> Self {
        Self::Failure(err)
    }
}

/// A test case failure.
pub struct Failure<'a> {
    case: &'a Case<'a>,
    err: anyhow::Error,
}

impl error::Error for Failure<'_> {}

impl fmt::Display for Failure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "test failure for `{}`: {}", self.case, self.err)
    }
}

impl fmt::Debug for Failure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub trait Backend {
    type Dec: Copy + fmt::Display + Sized;
    type Bits: Bits;

    fn from_bits(bits: Self::Bits) -> Self::Dec;
    fn parse(s: &str) -> Result<Self::Dec, ParseError>;
    fn mul(lhs: Self::Dec, rhs: Self::Dec) -> Self::Dec;
}

macro_rules! impl_dectest {
    ($name:ident, $ucoeff:ty, $dpd:ty) => {
        #[cfg(test)]
        impl Backend for $name {
            type Dec = $name;
            type Bits = $ucoeff;
            fn from_bits(bits: Self::Bits) -> $name {
                <$dpd>::from_bits(bits).to_bid128()
            }
            fn parse(s: &str) -> Result<$name, ParseError> {
                Self::parse(s)
            }
            fn mul(lhs: $name, rhs: $name) -> $name {
                lhs * rhs
            }
        }
    };
}
impl_dectest!(Bid128, u128, Dpd128);

pub trait Bits: Sized {
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
