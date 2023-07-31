use std::fmt::{Binary, Debug, LowerHex, UpperHex};
use std::hash::Hash;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not, Shl, ShlAssign, Shr, ShrAssign};

/// Represents a basic element whose bits can be manipulated and referenced.
///
/// It provides a common interface for all bit handling operations.
///
/// It has implementations for all numeric unsigned types.
pub trait BitsPrimitive
where
    Self: Sized + Copy + Eq + Ord + Hash + Default + Binary + LowerHex + UpperHex + Debug,
    Self: BitAnd<Output = Self>,
    Self: BitOr<Output = Self>,
    Self: BitAndAssign,
    Self: BitOrAssign,
    Self: Not<Output = Self>,
    Self: Shl<usize, Output = Self>,
    Self: Shr<usize, Output = Self>,
    Self: ShlAssign<usize>,
    Self: ShrAssign<usize>,
{
    const BIT_COUNT: usize;
    const ZERO: Self;
    const ONE: Self;

    fn from_u8(value: u8) -> Self;
    fn to_u8(self) -> u8;
}

macro_rules! impl_primitive {
    ($type:ty, $discriminant:ident) => {
        impl BitsPrimitive for $type {
            const BIT_COUNT: usize = <$type>::BITS as usize;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            fn from_u8(value: u8) -> Self {
                value as Self
            }

            fn to_u8(self) -> u8 {
                self as u8
            }
        }
    };
}

impl_primitive!(usize, Usize);
impl_primitive!(u8, U8);
impl_primitive!(u16, U16);
impl_primitive!(u32, U32);
impl_primitive!(u64, U64);
impl_primitive!(u128, U128);
