use std::fmt::Debug;
use std::ops::{BitAnd, BitAndAssign, Shr};

/// Represents a basic element whose bits can be manipulated and referenced.
///
/// It provides a common interface for all bit handling operations.
///
/// It has implementations for all numeric unsigned types.
pub trait BitsPrimitive
where
    Self: Sized + Copy + Eq + Debug,
    Self: BitAnd<Output = Self>,
    Self: BitAndAssign,
    Self: Shr<usize, Output = Self>,
{
    const DISCRIMINANT: BitsPrimitiveDiscriminant;
    const BIT_COUNT: usize;
    const ZERO: Self;
    const ONE: Self;
}

macro_rules! impl_primitive {
    ($type:ty, $discriminant:ident) => {
        impl BitsPrimitive for $type {
            const DISCRIMINANT: BitsPrimitiveDiscriminant =
                BitsPrimitiveDiscriminant::$discriminant;
            const BIT_COUNT: usize = <$type>::BITS as usize;
            const ZERO: Self = 0;
            const ONE: Self = 1;
        }
    };
}

impl_primitive!(usize, Usize);
impl_primitive!(u8, U8);
impl_primitive!(u16, U16);
impl_primitive!(u32, U32);
impl_primitive!(u64, U64);
impl_primitive!(u128, U128);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BitsPrimitiveDiscriminant {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}
