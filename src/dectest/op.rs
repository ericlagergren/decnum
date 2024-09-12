use std::fmt;

/// TODO
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
    CompareTotal {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
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
    Max {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
    Min {
        lhs: &'a str,
        rhs: &'a str,
        result: &'a str,
    },
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
            Self::CompareTotal { lhs, rhs, result } => {
                write!(f, "comparetotal {lhs} {rhs} -> {result}")
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
            Self::Max { lhs, rhs, result } => {
                write!(f, "max {lhs} {rhs} -> {result}")
            }
            Self::Min { lhs, rhs, result } => {
                write!(f, "min {lhs} {rhs} -> {result}")
            }
            Self::Multiply { lhs, rhs, result } => {
                write!(f, "multiply {lhs} {rhs} -> {result}")
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
