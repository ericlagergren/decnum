use core::marker::PhantomData;

use bitflags::bitflags;

/// TODO
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Ctx<D> {
    //traps: Condition,
    round: RoundingMode,
    _dec: PhantomData<D>,
}

impl<D> Default for Ctx<D> {
    fn default() -> Self {
        Self {
            //traps: Condition::default(),
            round: RoundingMode::default(),
            _dec: PhantomData,
        }
    }
}

/// TODO
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
pub enum RoundingMode {
    /// IEEE 754-2008 roundTiesToEven.
    #[default]
    ToNearestEven,
    /// IEEE 754-2008 roundTiesToAway.
    ToNearestAway,
    /// IEEE 754-2008 roundTowardZero.
    ToZero,
    /// No IEEE 754-2008 equivalent.
    AwayFromZero,
    /// IEEE 754-2008 roundTowardNegative.
    ToNegativeInf,
    /// IEEE 754-2008 roundTowardPositive.
    ToPositiveInf,
    /// No IEEE 754-2008 equivalent.
    ToNearestTowardZero,
}

impl RoundingMode {
    pub(super) fn try_from_str(s: &str) -> Option<Self> {
        let mode = match s {
            "half_even" => Self::ToNearestEven,
            "half_up" => Self::ToNearestAway,
            "down" => Self::ToZero,
            "floor" => Self::ToNegativeInf,
            "ceiling" => Self::ToPositiveInf,
            "half_down" => Self::ToNearestTowardZero,
            _ => return None,
        };
        Some(mode)
    }
}

/// An exceptional condition raised during or after an operation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Condition(u32);

impl Default for Condition {
    fn default() -> Self {
        !(Condition::INEXACT | Condition::ROUNDED | Condition::SUBNORMAL)
    }
}

bitflags! {
    impl Condition: u32 {
        /// Occurs if the exponent has been modified to fit the
        /// constraints of the decimal representation.
        const CLAMPED = 0x1;
        /// Occurs when a string is converted to a decimal and
        /// does not have a valid syntax.
        const CONVERSION_SYNTAX = 0x2;
        /// Occurs when division is attempted with a finite,
        /// non-zero dividend and a divisor with a value of zero.
        const DIVISION_BY_ZERO = 0x4;
        /// Occurs when the result of integer division would
        /// contain too many digits (i.e. be longer than the
        /// specified precision).
        const DIVISION_IMPOSSIBLE = 0x8;
        /// Occurs when division is attempted with in which both
        /// the divided and divisor are zero.
        const DIVISION_UNDEFINED = 0x10;
        /// Occurs when the result of an operation (e.g.
        /// division) is not exact, or when the
        /// [OVERFLOW][Condition::OVERFLOW] or
        /// [UNDERFLOW][Condition::UNDERFLOW] conditions occur.
        const INEXACT = 0x20;
        /// Occurs when the system doesn't have enough storage
        /// (i.e.  memory) to store the
        const INSUFFICIENT_STORAGE = 0x40;
        /// Occurs when an invalid context was detected during an
        /// operation. This might occur if, for example, an
        /// invalid [RoundingMode] is passed to a [Context].
        const INVALID_CONTEXT = 0x80;
        /// Occurs when:
        ///
        /// - An operand to an operation is a signaling NaN.
        /// - An attempt is made to add or subtract infinities of
        /// opposite signs.
        /// - An attempt is made to multiply zero by an infinity
        /// of either sign.
        /// - An attempt is made to divide an infinity by an
        /// infinity.
        /// - The divisor for a remainder operation is zero.
        /// - The dividend for a remainder operation is an
        /// infinity.
        /// - Either operand of the quantize operation is an
        /// infinity, or the result of a quantize operation would
        /// require greater precision than is available.
        /// - The operand of the ln or the log10 operation is
        /// less than zero.
        /// - The operand of the square-root operation has a sign
        /// of one and a non-zero coefficient.
        /// - Both operands of the power operation are zero, or
        /// if the left-hand operand is less than zero and the
        /// right-hand operand does not have an integral value or
        /// is an infinity.
        const INVALID_OPERATION = 0x100;
        /// Occurs when the adjusted exponent, after rounding,
        /// would be greater than the maximum allowed exponent.
        /// ([INEXACT][Condition::INEXACT] and
        /// [ROUNDED][Condition::ROUNDED] will also be raised.)
        const OVERFLOW = 0x200;
        /// Occurs when the result of an operation is rounded, or
        /// if an [OVERFLOW][Condition::OVERFLOW] or
        /// [UNDERFLOW][Condition::UNDERFLOW] occurs.
        const ROUNDED = 0x400;
        /// Ocurs when the result of a conversion or operation is
        /// subnormal (i.e. the adjusted exponent is less than
        /// the minimum allowed exponent before any rounding).
        const SUBNORMAL = 0x800;
        /// Occurs when the result is inexact and the adjusted
        /// exponent would be smaller (more negative) than the
        /// minimum allowed exponent.
        const UNDERFLOW = 0x1000;
    }
}
