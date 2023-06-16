use std::ptr::NonNull;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::{Bit, BitValue, BitsPrimitive};

/// A reference to a fixed-length sequence of bits anywhere in [underlying memory].
///
/// [underlying memory]: UnderlyingMemory
#[repr(C)]
pub struct BitStr {
    _unsized: [()],
}

impl BitStr {
    /// Creates a reference to the sequence of bits in the underlying memory.
    ///
    /// # Example
    ///
    /// ```
    /// use rust_bits::BitStr;
    ///
    /// let array = [0b10010011u8, 0b01101100u8];
    /// let bit_str: &BitStr = BitStr::new_ref(array.as_ref());
    /// assert_eq!(bit_str.len(), 16);
    /// ```
    #[inline]
    pub fn new_ref<U: BitsPrimitive>(under: &[U]) -> &Self {
        let components = TypedRefComponents {
            ptr: NonNull::from(&under[0]),
            offset: 0,
            bit_count: under.len() * U::BIT_COUNT,
        };
        let repr = components.encode();
        unsafe { std::mem::transmute(repr) }
    }

    /// Returns the number of referenced bits.
    #[inline]
    pub fn len(&self) -> usize {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        repr.decode().metadata.bit_count
    }

    /// Returns the same as `self.len() == 0`.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the value of a bit.
    ///
    /// `None` is returned if the index is out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<BitValue> {
        self.get_ref(index).map(|bit_ref| bit_ref.read())
    }

    /// Returns the reference of a bit.
    ///
    /// `None` is returned if the index is out of bounds.
    #[inline]
    pub fn get_ref(&self, index: usize) -> Option<&Bit> {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let mut components = repr.decode();
        if index < components.metadata.bit_count {
            components.metadata.offset += index;
            components.metadata.bit_count = 1;
            let repr = components.encode();
            let bit_ref = unsafe { std::mem::transmute(repr) };
            Some(bit_ref)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ptr::NonNull;

    use crate::refrepr::RefRepr;
    use crate::BitValue::{One, Zero};
    use crate::{Bit, BitStr, BitsPrimitive};

    #[test]
    fn new_ref() {
        const N: usize = 3;

        macro_rules! assert_new_ref_with_type {
            ($type:ty) => {
                let memory: [$type; N] = [<$type>::ZERO, <$type>::ZERO, <$type>::ZERO];

                let bit_str: &BitStr = BitStr::new_ref(&memory);

                assert_eq!(bit_str.len(), N * <$type>::BIT_COUNT);
                let components = unsafe { std::mem::transmute::<_, RefRepr>(bit_str) }.decode();
                assert_eq!(components.ptr, NonNull::from(&memory).cast());
                assert_eq!(
                    components.metadata.underlying_primitive,
                    <$type>::DISCRIMINANT
                );
                assert_eq!(components.metadata.offset, 0);
                assert_eq!(components.metadata.bit_count, N * <$type>::BIT_COUNT);
            };
        }

        assert_new_ref_with_type!(usize);
        assert_new_ref_with_type!(u8);
        assert_new_ref_with_type!(u16);
        assert_new_ref_with_type!(u32);
        assert_new_ref_with_type!(u64);
        assert_new_ref_with_type!(u128);
    }

    #[test]
    fn get() {
        let memory: [u8; 2] = [0b10010011, 0b01101100];
        let bit_str = BitStr::new_ref(memory.as_ref());

        assert_eq!(bit_str.get(0), Some(One));
        assert_eq!(bit_str.get(1), Some(One));
        assert_eq!(bit_str.get(2), Some(Zero));
        assert_eq!(bit_str.get(3), Some(Zero));
        assert_eq!(bit_str.get(4), Some(One));
        assert_eq!(bit_str.get(5), Some(Zero));
        assert_eq!(bit_str.get(6), Some(Zero));
        assert_eq!(bit_str.get(7), Some(One));

        assert_eq!(bit_str.get(8), Some(Zero));
        assert_eq!(bit_str.get(9), Some(Zero));
        assert_eq!(bit_str.get(10), Some(One));
        assert_eq!(bit_str.get(11), Some(One));
        assert_eq!(bit_str.get(12), Some(Zero));
        assert_eq!(bit_str.get(13), Some(One));
        assert_eq!(bit_str.get(14), Some(One));
        assert_eq!(bit_str.get(15), Some(Zero));

        assert_eq!(bit_str.get(16), None);
        assert_eq!(bit_str.get(17), None);
        assert_eq!(bit_str.get(18), None);
    }

    #[test]
    fn get_ref() {
        let memory: [u8; 2] = [0b10010011, 0b01101100];
        let bit_str = BitStr::new_ref(memory.as_ref());

        let bit_ref: Option<&Bit> = bit_str.get_ref(0);
        assert_eq!(bit_ref.unwrap().read(), One);
        assert_eq!(bit_str.get_ref(1).unwrap().read(), One);
        assert_eq!(bit_str.get_ref(2).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(3).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(4).unwrap().read(), One);
        assert_eq!(bit_str.get_ref(5).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(6).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(7).unwrap().read(), One);

        assert_eq!(bit_str.get_ref(8).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(9).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(10).unwrap().read(), One);
        assert_eq!(bit_str.get_ref(11).unwrap().read(), One);
        assert_eq!(bit_str.get_ref(12).unwrap().read(), Zero);
        assert_eq!(bit_str.get_ref(13).unwrap().read(), One);
        assert_eq!(bit_str.get_ref(14).unwrap().read(), One);
        assert_eq!(bit_str.get_ref(15).unwrap().read(), Zero);

        assert_eq!(bit_str.get_ref(16), None);
        assert_eq!(bit_str.get_ref(17), None);
        assert_eq!(bit_str.get_ref(18), None);
    }
}
