use std::ops::{BitAnd, BitAndAssign, BitOrAssign, Not, Shl};

pub(crate) const DISCRIMINANT_BIT_COUNT: usize = 3;

pub(crate) const DISCRIMINANT_MASK: usize = 0b0111;

pub trait PrimitiveType: Copy + PartialEq
where
    Self: Not<Output = Self>,
    Self: BitAnd<Output = Self>,
    Self: BitAndAssign<Self>,
    Self: BitOrAssign<Self>,
    Self: Shl<usize, Output = Self>,
{
    const DISCRIMINANT: usize;
    const BIT_COUNT: usize;
    const ZERO: Self;
    const ONE: Self;
}

impl PrimitiveType for usize {
    const DISCRIMINANT: usize = 0;
    const BIT_COUNT: usize = Self::BITS as usize;
    const ZERO: Self = 0;
    const ONE: Self = 1;
}

impl PrimitiveType for u8 {
    const DISCRIMINANT: usize = 1;
    const BIT_COUNT: usize = Self::BITS as usize;
    const ZERO: Self = 0;
    const ONE: Self = 1;
}

impl PrimitiveType for u16 {
    const DISCRIMINANT: usize = 2;
    const BIT_COUNT: usize = Self::BITS as usize;
    const ZERO: Self = 0;
    const ONE: Self = 1;
}

impl PrimitiveType for u32 {
    const DISCRIMINANT: usize = 3;
    const BIT_COUNT: usize = Self::BITS as usize;
    const ZERO: Self = 0;
    const ONE: Self = 1;
}

impl PrimitiveType for u64 {
    const DISCRIMINANT: usize = 4;
    const BIT_COUNT: usize = Self::BITS as usize;
    const ZERO: Self = 0;
    const ONE: Self = 1;
}

impl PrimitiveType for u128 {
    const DISCRIMINANT: usize = 5;
    const BIT_COUNT: usize = Self::BITS as usize;
    const ZERO: Self = 0;
    const ONE: Self = 1;
}
