use std::fmt::{Binary, Debug, Display, LowerExp, LowerHex, UpperExp, UpperHex};
use std::hash::Hash;
use std::ops::{BitAnd, BitAndAssign, BitOrAssign, Not, Shl, ShlAssign, ShrAssign};

pub trait PrimitiveType:
    Copy
    + Eq
    + PartialOrd
    + Ord
    + Hash
    + Display
    + Debug
    + Binary
    + LowerHex
    + UpperHex
    + LowerExp
    + UpperExp
where
    Self: Not<Output = Self>,
    Self: BitAnd<Output = Self>,
    Self: BitAndAssign<Self>,
    Self: BitOrAssign<Self>,
    Self: Shl<usize, Output = Self>,
    Self: ShlAssign<usize>,
    Self: ShrAssign<usize>,
{
    const DISCRIMINANT: Discriminant;
    const BIT_COUNT: usize;
    const ZERO: Self;
    const ONE: Self;

    fn to_usize(self) -> usize;
    fn from_usize(n: usize) -> Self;
}

macro_rules! impl_primitive_type {
    ($t:ty, $discriminant_name:ident) => {
        impl PrimitiveType for $t {
            const DISCRIMINANT: Discriminant = Discriminant::$discriminant_name;
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

impl_primitive_type!(usize, Usize);
impl_primitive_type!(u8, U8);
impl_primitive_type!(u16, U16);
impl_primitive_type!(u32, U32);
impl_primitive_type!(u64, U64);
impl_primitive_type!(u128, U128);

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Discriminant {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl Discriminant {
    pub(crate) const BIT_COUNT: usize = 3;

    pub(crate) const VALUES: [Self; 6] = [
        Self::Usize,
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
        Self::U128,
    ];

    pub(crate) fn execute<E: DiscriminantExecutor>(self, executor: E) -> E::Output {
        match self {
            usize::DISCRIMINANT => executor.execute::<usize>(),
            u8::DISCRIMINANT => executor.execute::<u8>(),
            u16::DISCRIMINANT => executor.execute::<u16>(),
            u32::DISCRIMINANT => executor.execute::<u32>(),
            u64::DISCRIMINANT => executor.execute::<u64>(),
            u128::DISCRIMINANT => executor.execute::<u128>(),
        }
    }
}

pub(crate) trait DiscriminantExecutor {
    type Output;
    fn execute<U: PrimitiveType>(self) -> Self::Output;
}
