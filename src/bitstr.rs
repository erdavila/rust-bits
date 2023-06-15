use std::ptr::NonNull;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::BitsPrimitive;

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
}

#[cfg(test)]
mod tests {
    use std::ptr::NonNull;

    use crate::refrepr::RefRepr;
    use crate::{BitStr, BitsPrimitive};

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
}
