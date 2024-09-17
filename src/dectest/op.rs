use std::fmt;

/// TODO
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[allow(dead_code, reason = "TODO")]
pub enum Op<'a> {
    Abs { input: &'a str },
    Add { lhs: &'a str, rhs: &'a str },
    And { lhs: &'a str, rhs: &'a str },
    Apply { input: &'a str },
    Canonical { input: &'a str },
    Class { input: &'a str },
    Compare { lhs: &'a str, rhs: &'a str },
    CompareSig { lhs: &'a str, rhs: &'a str },
    CompareTotal { lhs: &'a str, rhs: &'a str },
    CompareTotalMag { lhs: &'a str, rhs: &'a str },
    Copy { input: &'a str },
    CopyAbs { input: &'a str },
    CopyNegate { input: &'a str },
    CopySign { lhs: &'a str, rhs: &'a str },
    Divide { lhs: &'a str, rhs: &'a str },
    DivideInt { lhs: &'a str, rhs: &'a str },
    Exp { input: &'a str },
    Fma { a: &'a str, b: &'a str, c: &'a str },
    Invert { input: &'a str },
    Ln { input: &'a str },
    Log10 { input: &'a str },
    Logb { input: &'a str },
    Max { lhs: &'a str, rhs: &'a str },
    MaxMag { lhs: &'a str, rhs: &'a str },
    Min { lhs: &'a str, rhs: &'a str },
    MinMag { lhs: &'a str, rhs: &'a str },
    Minus { input: &'a str },
    Multiply { lhs: &'a str, rhs: &'a str },
    NextMinus { input: &'a str },
    NextPlus { input: &'a str },
    NextToward { lhs: &'a str, rhs: &'a str },
    Or { lhs: &'a str, rhs: &'a str },
    Plus { input: &'a str },
    Power { lhs: &'a str, rhs: &'a str },
    Quantize { lhs: &'a str, rhs: &'a str },
    Reduce { input: &'a str },
    Remainder { lhs: &'a str, rhs: &'a str },
    RemainderNear { lhs: &'a str, rhs: &'a str },
    Rescale { lhs: &'a str, rhs: &'a str },
    Rotate { lhs: &'a str, rhs: &'a str },
    SameQuantum { lhs: &'a str, rhs: &'a str },
    Scaleb { lhs: &'a str, rhs: &'a str },
    Shift { lhs: &'a str, rhs: &'a str },
    SquareRoot { input: &'a str },
    Subtract { lhs: &'a str, rhs: &'a str },
    ToEng { input: &'a str },
    ToIntegral { input: &'a str },
    ToIntegralX { input: &'a str },
    ToSci { input: &'a str },
    Trim { input: &'a str },
    Xor { lhs: &'a str, rhs: &'a str },
}

impl Op<'_> {
    const fn name(&self) -> &'static str {
        use Op::*;
        match self {
            Abs { .. } => "abs",
            Add { .. } => "add",
            And { .. } => "and",
            Apply { .. } => "apply",
            Canonical { .. } => "canonical",
            Class { .. } => "class",
            Compare { .. } => "compare",
            CompareSig { .. } => "comparesig",
            CompareTotal { .. } => "comparetotal",
            CompareTotalMag { .. } => "comparetotmag",
            Copy { .. } => "copy",
            CopyAbs { .. } => "copyabs",
            CopyNegate { .. } => "copynegate",
            CopySign { .. } => "copysign",
            Divide { .. } => "divide",
            DivideInt { .. } => "divideint",
            Exp { .. } => "exp",
            Fma { .. } => "fma",
            Invert { .. } => "invert",
            Ln { .. } => "ln",
            Log10 { .. } => "log10",
            Logb { .. } => "logb",
            Max { .. } => "max",
            Min { .. } => "min",
            MaxMag { .. } => "maxmag",
            MinMag { .. } => "minmag",
            Minus { .. } => "minus",
            Multiply { .. } => "multiply",
            NextMinus { .. } => "nextminus",
            NextPlus { .. } => "nextplus",
            NextToward { .. } => "nexttoward",
            Or { .. } => "or",
            Plus { .. } => "plus",
            Power { .. } => "power",
            Quantize { .. } => "quantize",
            Reduce { .. } => "reduce",
            Remainder { .. } => "remainder",
            RemainderNear { .. } => "remaindernear",
            Rescale { .. } => "rescale",
            Rotate { .. } => "rotate",
            SameQuantum { .. } => "samequantum",
            Scaleb { .. } => "scaleb",
            Shift { .. } => "shift",
            SquareRoot { .. } => "squareroot",
            Subtract { .. } => "subtract",
            ToEng { .. } => "toeng",
            ToIntegral { .. } => "tointegral",
            ToIntegralX { .. } => "tointegralx",
            ToSci { .. } => "tosci",
            Trim { .. } => "trim",
            Xor { .. } => "xor",
        }
    }
}

impl fmt::Display for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = self.name();
        use Op::*;
        match self {
            // Unary.
            Abs { input }
            | Apply { input }
            | Canonical { input }
            | Class { input }
            | Copy { input }
            | CopyAbs { input }
            | CopyNegate { input }
            | Exp { input }
            | Invert { input }
            | Ln { input }
            | Log10 { input }
            | Logb { input }
            | Minus { input }
            | NextMinus { input }
            | NextPlus { input }
            | Plus { input }
            | Reduce { input }
            | SquareRoot { input }
            | ToEng { input }
            | ToIntegral { input }
            | ToIntegralX { input }
            | ToSci { input }
            | Trim { input } => {
                write!(f, "{name} {input}")
            }

            // Binary.
            Add { lhs, rhs }
            | And { lhs, rhs }
            | Compare { lhs, rhs }
            | CompareSig { lhs, rhs }
            | CompareTotal { lhs, rhs }
            | CompareTotalMag { lhs, rhs }
            | CopySign { lhs, rhs }
            | Divide { lhs, rhs }
            | DivideInt { lhs, rhs }
            | Max { lhs, rhs }
            | MaxMag { lhs, rhs }
            | Min { lhs, rhs }
            | MinMag { lhs, rhs }
            | Multiply { lhs, rhs }
            | NextToward { lhs, rhs }
            | Or { lhs, rhs }
            | Power { lhs, rhs }
            | Quantize { lhs, rhs }
            | Remainder { lhs, rhs }
            | RemainderNear { lhs, rhs }
            | Rescale { lhs, rhs }
            | Rotate { lhs, rhs }
            | SameQuantum { lhs, rhs }
            | Scaleb { lhs, rhs }
            | Shift { lhs, rhs }
            | Subtract { lhs, rhs }
            | Xor { lhs, rhs } => write!(f, "{name} {lhs} {rhs}"),

            // Ternary.
            Fma { a, b, c } => write!(f, "{name} {a} {b} {c}"),
        }
    }
}
