// Bitflags
#![allow(clippy::indexing_slicing)]

use core::marker::PhantomData;

use bitflags::bitflags;

/// TODO
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Ctx<D> {
    //traps: Condition,
    pub(crate) rounding: RoundingMode,
    pub(crate) _dec: PhantomData<D>,
}

impl<D> Ctx<D> {
    /// TODO
    pub const fn new() -> Self {
        Self {
            //traps: Condition::default(),
            rounding: RoundingMode::ToNearestEven,
            _dec: PhantomData,
        }
    }
    /// TODO
    pub const fn with_rounding_mode(self, mode: RoundingMode) -> Self {
        let mut ctx = self;
        ctx.rounding = mode;
        ctx
    }
}

impl<D> Default for Ctx<D> {
    fn default() -> Self {
        Self::new()
    }
}

/// TODO
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
pub enum RoundingMode {
    /// IEEE 754-2008 roundTiesToEven.
    ///
    /// - Under 0.5 rounds down.
    /// - Over 0.5 rounds up.
    /// - Exactly 0.5 rounds to the nearest even.
    #[default]
    ToNearestEven,
    /// IEEE 754-2008 roundTiesToAway.
    ///
    /// Like [`ToNearestEven`][Self::ToNearestEven], except that
    /// 0.5 rounds up.
    ToNearestAway,
    /// IEEE 754-2008 roundTowardZero.
    ///
    /// AKA truncation.
    ToZero,
    /// No IEEE 754-2008 equivalent.
    ///
    /// Rounds up if the discarded digits are non-zero.
    AwayFromZero,
    /// IEEE 754-2008 roundTowardNegative.
    ///
    /// AKA floor.
    ToNegativeInf,
    /// IEEE 754-2008 roundTowardPositive.
    ///
    /// AKA ceiling.
    ToPositiveInf,
    /// No IEEE 754-2008 equivalent.
    ///
    /// Like [`ToNearestAway`][Self::ToNearestAway], except that
    /// 0.5 rounds down.
    ToNearestTowardZero,
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
