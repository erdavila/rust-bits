use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

/// Represents the value of a bit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Debug)]
#[repr(u8)]
pub enum BitValue {
    /// The bit value of `0`.
    #[default]
    Zero,

    /// The bit value of `1`.
    One,
}

impl BitValue {
    /// Converts the `BitValue` to a `bool`.
    pub fn to_bool(self) -> bool {
        match self {
            BitValue::Zero => false,
            BitValue::One => true,
        }
    }
}

impl From<bool> for BitValue {
    /// Creates a `BitValue` from a `bool`.
    fn from(value: bool) -> Self {
        match value {
            true => Self::One,
            false => Self::Zero,
        }
    }
}

impl Not for BitValue {
    type Output = Self;

    fn not(self) -> Self::Output {
        BitValue::from(!self.to_bool())
    }
}

macro_rules! impl_binary_operation {
    ($operation:ident $method:ident $operator:tt, $assign_operation:ident $assign_method:ident $assign_operator:tt) => {
        // BitValue OP BitValue
        impl $operation for BitValue {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self::Output {
                BitValue::from(self.to_bool() $operator rhs.to_bool())
            }
        }

        // BitValue OP= BitValue
        impl $assign_operation for BitValue {
            fn $assign_method(&mut self, rhs: Self) {
                *self = *self $operator rhs;
            }
        }

        // BitValue OP= bool
        impl $assign_operation<bool> for BitValue {
            fn $assign_method(&mut self, rhs: bool) {
                *self $assign_operator BitValue::from(rhs);
            }
        }

        // bool OP= BitValue
        impl $assign_operation<BitValue> for bool {
            fn $assign_method(&mut self, rhs: BitValue) {
                *self $assign_operator rhs.to_bool();
            }
        }
    };
}

impl_binary_operation!(BitAnd bitand &, BitAndAssign bitand_assign &=);
impl_binary_operation!(BitOr bitor |, BitOrAssign bitor_assign |=);
impl_binary_operation!(BitXor bitxor ^, BitXorAssign bitxor_assign ^=);

#[cfg(test)]
mod tests {
    use crate::BitValue::{One, Zero};

    macro_rules! assert_binary_operation {
        ($operand1:tt $operator:tt $operand2:tt == $expected:expr, $assign_operator:tt) => {
            // BitValue OP BitValue
            assert_eq!($operand1 $operator $operand2, $expected);

            // BitValue OP= BitValue
            let mut var = $operand1;
            var $assign_operator $operand2;
            assert_eq!(var, $expected);

            // BitValue OP= bool
            let mut var = $operand1;
            var $assign_operator $operand2.to_bool();
            assert_eq!(var, $expected);

            // bool OP= BitValue
            let mut var = $operand1.to_bool();
            var $assign_operator $operand2;
            assert_eq!(var, $expected.to_bool());
        };
    }

    #[test]
    fn not() {
        assert_eq!(!Zero, One);
        assert_eq!(!One, Zero);
    }

    #[test]
    fn and() {
        assert_binary_operation!(Zero & Zero == Zero, &=);
        assert_binary_operation!(Zero & One == Zero, &=);
        assert_binary_operation!(One & Zero == Zero, &=);
        assert_binary_operation!(One & One == One, &=);
    }

    #[test]
    fn or() {
        assert_binary_operation!(Zero | Zero == Zero, |=);
        assert_binary_operation!(Zero | One == One, |=);
        assert_binary_operation!(One | Zero == One, |=);
        assert_binary_operation!(One | One == One, |=);
    }

    #[test]
    fn xor() {
        assert_binary_operation!(Zero ^ Zero == Zero, ^=);
        assert_binary_operation!(Zero ^ One == One, ^=);
        assert_binary_operation!(One ^ Zero == One, ^=);
        assert_binary_operation!(One ^ One == Zero, ^=);
    }

    #[test]
    fn cmp() {
        assert!(Zero < One);
    }
}
