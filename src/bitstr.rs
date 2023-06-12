use std::marker::PhantomData;

use crate::refs::{
    DstMutRefRepr, DstMutRefReprExecutor, DstRefRepr, DstRefReprExecutor, MutRefComponents,
    RefComponents,
};
use crate::{Bit, BitValue, PrimitiveType, UnderlyingPrimitives};

/// A reference to a fixed-size sequence of bits anywhere in underlying
/// [primitives].
///
/// [primitives]: crate::PrimitiveType
#[repr(C)]
#[derive(Eq)]
pub struct BitStr {
    _unsized: [()],
}

impl BitStr {
    /// Creates a reference to the sequence of bits in the underlying primitives.
    pub fn new_ref<U: UnderlyingPrimitives + ?Sized>(under: &U) -> &Self {
        let repr = DstRefRepr::encode(under, 0, under.bit_count());
        unsafe { std::mem::transmute(repr) }
    }

    /// Creates a reference to the sequence of mutable bits in the underlying
    /// primitives.
    pub fn new_mut<U: UnderlyingPrimitives + ?Sized>(under: &mut U) -> &mut Self {
        let repr = DstMutRefRepr::encode(under, 0, under.bit_count());
        unsafe { std::mem::transmute(repr) }
    }

    /// Returns the number of referenced bits.
    pub fn len(&self) -> usize {
        struct Executor;
        impl DstRefReprExecutor<'_> for Executor {
            type Output = usize;
            fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output {
                components.bit_count
            }
        }
        self.repr().decode_and_execute(Executor)
    }

    /// Returns the same as `self.len() == 0`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the value of the bit at the specified index.
    ///
    /// Returns `None` if the index is invalid.
    pub fn at(&self, index: usize) -> Option<BitValue> {
        self.at_ref(index).map(|bit_ref| bit_ref.get())
    }

    /// Returns a reference to the bit at the specified index.
    ///
    /// Returns `None` if the index is invalid.
    pub fn at_ref(&self, index: usize) -> Option<&Bit> {
        struct Executor<'a> {
            index: usize,
            phantom: PhantomData<&'a ()>,
        }
        impl<'a> DstRefReprExecutor<'a> for Executor<'a> {
            type Output = Option<&'a Bit>;

            fn execute<U: PrimitiveType + 'a>(
                self,
                components: RefComponents<'a, U>,
            ) -> Self::Output {
                let bit_index = components.offset + self.index;
                if bit_index < components.bit_count {
                    let bit_ref = Bit::new_ref(components.get_ref(), bit_index);
                    Some(bit_ref)
                } else {
                    None
                }
            }
        }

        self.repr().decode_and_execute(Executor {
            index,
            phantom: PhantomData,
        })
    }

    /// Returns a mutable reference to the bit at the specified index.
    ///
    /// Returns `None` if the index is invalid.
    pub fn at_mut(&mut self, index: usize) -> Option<&mut Bit> {
        struct Executor<'a> {
            index: usize,
            phantom: PhantomData<&'a mut ()>,
        }
        impl<'a> DstMutRefReprExecutor<'a> for Executor<'a> {
            type Output = Option<&'a mut Bit>;

            fn execute<U: PrimitiveType + 'a>(
                self,
                mut components: MutRefComponents<'a, U>,
            ) -> Self::Output {
                let bit_index = components.offset + self.index;
                if bit_index < components.bit_count {
                    let bit_ref = Bit::new_mut(components.get_ref(), bit_index);
                    Some(bit_ref)
                } else {
                    None
                }
            }
        }

        self.repr_mut().decode_and_execute(Executor {
            index,
            phantom: PhantomData,
        })
    }

    fn repr(&self) -> DstRefRepr {
        unsafe { std::mem::transmute(self) }
    }

    fn repr_mut(&mut self) -> DstMutRefRepr {
        unsafe { std::mem::transmute(self) }
    }
}

impl PartialEq for BitStr {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && {
            // TODO: implement a more optimized comparison
            for i in 0..self.len() {
                if self.at(i) != other.at(i) {
                    return false;
                }
            }
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Not;

    use crate::{BitStr, BitValue, PrimitiveType};
    use BitValue::{One, Zero};

    #[test]
    fn new_ref() {
        macro_rules! assert_len {
            ($type:ty) => {
                let under: $type = 1;
                let bit_str: &BitStr = BitStr::new_ref(&under);
                assert_eq!(bit_str.len(), <$type>::BIT_COUNT);

                let under: [$type; 3] = [1, 2, 3];
                let bit_str: &BitStr = BitStr::new_ref(&under);
                assert_eq!(bit_str.len(), <$type>::BIT_COUNT * 3);

                let under: &[$type] = &under;
                let bit_str: &BitStr = BitStr::new_ref(under);
                assert_eq!(bit_str.len(), <$type>::BIT_COUNT * 3);
            };
        }

        assert_len!(usize);
        assert_len!(u8);
        assert_len!(u16);
        assert_len!(u32);
        assert_len!(u64);
        assert_len!(u128);
    }

    #[test]
    fn at() {
        let under = 0b10010011u8;
        let bit_str = BitStr::new_ref(&under);

        assert_eq!(bit_str.at(0), Some(One));
        assert_eq!(bit_str.at(1), Some(One));
        assert_eq!(bit_str.at(2), Some(Zero));
        assert_eq!(bit_str.at(3), Some(Zero));
        assert_eq!(bit_str.at(4), Some(One));
        assert_eq!(bit_str.at(5), Some(Zero));
        assert_eq!(bit_str.at(6), Some(Zero));
        assert_eq!(bit_str.at(7), Some(One));
        assert_eq!(bit_str.at(8), None);
    }

    #[test]
    fn at_ref() {
        let under = 0b10010011u8;
        let bit_str = BitStr::new_ref(&under);

        assert_eq!(bit_str.at_ref(0).unwrap().get(), One);
        assert_eq!(bit_str.at_ref(1).unwrap().get(), One);
        assert_eq!(bit_str.at_ref(2).unwrap().get(), Zero);
        assert_eq!(bit_str.at_ref(3).unwrap().get(), Zero);
        assert_eq!(bit_str.at_ref(4).unwrap().get(), One);
        assert_eq!(bit_str.at_ref(5).unwrap().get(), Zero);
        assert_eq!(bit_str.at_ref(6).unwrap().get(), Zero);
        assert_eq!(bit_str.at_ref(7).unwrap().get(), One);
        assert_eq!(bit_str.at_ref(8), None);
    }

    #[test]
    fn at_mut() {
        let mut under = 0b10010011u8;
        let bit_str = BitStr::new_mut(&mut under);

        assert_eq!(bit_str.at_mut(0).unwrap().get(), One);
        assert_eq!(bit_str.at_mut(1).unwrap().get(), One);
        assert_eq!(bit_str.at_mut(2).unwrap().get(), Zero);
        assert_eq!(bit_str.at_mut(3).unwrap().get(), Zero);
        assert_eq!(bit_str.at_mut(4).unwrap().get(), One);
        assert_eq!(bit_str.at_mut(5).unwrap().get(), Zero);
        assert_eq!(bit_str.at_mut(6).unwrap().get(), Zero);
        assert_eq!(bit_str.at_mut(7).unwrap().get(), One);
        assert_eq!(bit_str.at_mut(8), None);

        bit_str.at_mut(3).unwrap().modify(Not::not);
        bit_str.at_mut(4).unwrap().modify(Not::not);

        assert_eq!(under, 0b10001011);
    }

    #[test]
    fn eq() {
        let under1 = 0b10010011u8;
        let under2 = 0b10010011u8;
        let under3 = 0b01101100u8;

        let bit_str1 = BitStr::new_ref(&under1);
        let bit_str2 = BitStr::new_ref(&under2);
        let bit_str3 = BitStr::new_ref(&under3);

        assert!(bit_str1 == bit_str1);
        assert!(bit_str1 == bit_str2);
        assert!(bit_str1 != bit_str3);


        // TODO: compare with String
        // TODO: compare with &String
    }
}
