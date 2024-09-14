use std::fmt;

/// TODO
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op<'a> {
    Abs { input: &'a str },
    Add { lhs: &'a str, rhs: &'a str },
    And,
    Apply { input: &'a str },
    Canonical { input: &'a str },
    Class,
    Compare { lhs: &'a str, rhs: &'a str },
    CompareSig { lhs: &'a str, rhs: &'a str },
    CompareTotal { lhs: &'a str, rhs: &'a str },
    CompareTotMag,
    Copy { input: &'a str },
    CopyAbs { input: &'a str },
    CopyNegate { input: &'a str },
    CopySign { lhs: &'a str, rhs: &'a str },
    Divide,
    DivideInt,
    Exp,
    Fma,
    Invert,
    Ln,
    Log10,
    Logb,
    Max { lhs: &'a str, rhs: &'a str },
    Min { lhs: &'a str, rhs: &'a str },
    MaxMag,
    MinMag,
    Minus,
    Multiply { lhs: &'a str, rhs: &'a str },
    NextMinus,
    NextPlus,
    NextToward,
    Or,
    Plus,
    Power,
    Quantize { lhs: &'a str, rhs: &'a str },
    Reduce,
    Remainder,
    Remaindernear,
    Rescale,
    Rotate,
    SameQuantum,
    Scaleb,
    Shift,
    SquareRoot,
    Subtract { lhs: &'a str, rhs: &'a str },
    ToEng,
    ToIntegral,
    ToIntegralX { input: &'a str },
    ToSci,
    Trim,
    Xor,
}

impl fmt::Display for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Abs { input } => {
                write!(f, "abs {input}")
            }
            Self::Add { lhs, rhs } => {
                write!(f, "add {lhs} {rhs}")
            }
            Self::Apply { input } => {
                write!(f, "apply {input}")
            }
            Self::Canonical { input } => {
                write!(f, "canonical {input}")
            }
            Self::Compare { lhs, rhs } => {
                write!(f, "compare {lhs} {rhs}")
            }
            Self::CompareSig { lhs, rhs } => {
                write!(f, "comparesig {lhs} {rhs}")
            }
            Self::CompareTotal { lhs, rhs } => {
                write!(f, "comparetotal {lhs} {rhs}")
            }
            Self::Copy { input } => {
                write!(f, "copy {input}")
            }
            Self::CopyAbs { input } => {
                write!(f, "copyabs {input}")
            }
            Self::CopyNegate { input } => {
                write!(f, "copynegate {input}")
            }
            Self::CopySign { lhs, rhs } => {
                write!(f, "copysign {lhs} {rhs}")
            }
            Self::Max { lhs, rhs } => {
                write!(f, "max {lhs} {rhs}")
            }
            Self::Min { lhs, rhs } => {
                write!(f, "min {lhs} {rhs}")
            }
            Self::Multiply { lhs, rhs } => {
                write!(f, "multiply {lhs} {rhs}")
            }
            Self::Quantize { lhs, rhs } => {
                write!(f, "quantize {lhs} {rhs}")
            }
            Self::Subtract { lhs, rhs } => {
                write!(f, "subtract {lhs} {rhs}")
            }
            Self::ToIntegralX { input } => {
                write!(f, "tointegralx {input}")
            }
            _ => write!(f, "other op"),
        }
    }
}
