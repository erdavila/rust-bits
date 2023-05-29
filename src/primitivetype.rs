use std::fmt::{LowerHex, UpperHex};
use std::ops::{BitAnd, BitAndAssign, BitOrAssign, Not, Shl, ShlAssign, ShrAssign};

pub(crate) const DISCRIMINANT_BIT_COUNT: usize = 3;

pub(crate) const DISCRIMINANT_MASK: usize = 0b0111;

pub trait PrimitiveType: Copy + PartialEq + LowerHex + UpperHex
where
    Self: Not<Output = Self>,
    Self: BitAnd<Output = Self>,
    Self: BitAndAssign<Self>,
    Self: BitOrAssign<Self>,
    Self: Shl<usize, Output = Self>,
    Self: ShlAssign<usize>,
    Self: ShrAssign<usize>,
{
    const DISCRIMINANT: usize;
    const BIT_COUNT: usize;
    const ZERO: Self;
    const ONE: Self;

    fn to_usize(self) -> usize;
    fn from_usize(n: usize) -> Self;
}

macro_rules! impl_primitive_type {
    ($t:ty, $discriminant:literal) => {
        impl PrimitiveType for $t {
            const DISCRIMINANT: usize = $discriminant;
            const BIT_COUNT: usize = Self::BITS as usize;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            fn to_usize(self) -> usize {
                self as usize
            }

            fn from_usize(n: usize) -> Self {
                n as Self
            }
        }
    };
}

impl_primitive_type!(usize, 0);
impl_primitive_type!(u8, 1);
impl_primitive_type!(u16, 2);
impl_primitive_type!(u32, 3);
impl_primitive_type!(u64, 4);
impl_primitive_type!(u128, 5);
