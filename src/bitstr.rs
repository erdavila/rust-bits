use std::ops::{Index, IndexMut};
use std::ptr::NonNull;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::{Bit, BitValue, BitsPrimitive};

/// A reference to a fixed-length sequence of bits anywhere in [underlying memory].
///
/// [underlying memory]: UnderlyingMemory
#[repr(C)]
#[derive(Eq)]
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
        let repr = Self::new_repr(under);
        unsafe { std::mem::transmute(repr) }
    }

    /// Creates a mutable reference to the sequence of bits in the underlying memory.
    ///
    /// # Example
    ///
    /// ```
    /// use rust_bits::BitStr;
    ///
    /// let mut array = [0b10010011u8, 0b01101100u8];
    /// let bit_str: &BitStr = BitStr::new_mut(array.as_mut());
    /// assert_eq!(bit_str.len(), 16);
    /// ```
    #[inline]
    pub fn new_mut<U: BitsPrimitive>(under: &mut [U]) -> &mut Self {
        let repr = Self::new_repr(under);
        unsafe { std::mem::transmute(repr) }
    }

    #[inline]
    fn new_repr<U: BitsPrimitive>(under: &[U]) -> RefRepr {
        let components = TypedRefComponents {
            ptr: NonNull::from(&under[0]),
            offset: 0,
            bit_count: under.len() * U::BIT_COUNT,
        };
        components.encode()
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

    /// Returns a reference to a bit.
    ///
    /// `None` is returned if the index is out of bounds.
    #[inline]
    pub fn get_ref(&self, index: usize) -> Option<&Bit> {
        self.get_bit_ref_repr(index)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    /// Returns a mutable reference to a bit.
    ///
    /// `None` is returned if the index is out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut Bit> {
        self.get_bit_ref_repr(index)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn get_bit_ref_repr(&self, index: usize) -> Option<RefRepr> {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let mut components = repr.decode();
        if index < components.metadata.bit_count {
            components.metadata.offset += index;
            components.metadata.bit_count = 1;
            let repr = components.encode();
            Some(repr)
        } else {
            None
        }
    }
}

impl Index<usize> for BitStr {
    type Output = Bit;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get_ref(index).expect("invalid index")
    }
}

impl IndexMut<usize> for BitStr {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).expect("invalid index")
    }
}

impl PartialEq for BitStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // TODO: optimize it

        for i in 0..self.len() {
            if self.get(i) != other.get(i) {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use std::convert::identity;
    use std::ops::Not;
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

    #[test]
    fn get_mut() {
        let mut memory: [u8; 1] = [0b10010011];
        let bit_str = BitStr::new_mut(&mut memory);

        let bit_ref: Option<&mut Bit> = bit_str.get_mut(0);
        assert_eq!(bit_ref.unwrap().read(), One);
        assert_eq!(bit_str.get_mut(1).unwrap().read(), One);
        assert_eq!(bit_str.get_mut(2).unwrap().read(), Zero);
        assert_eq!(bit_str.get_mut(3).unwrap().read(), Zero);
        assert_eq!(bit_str.get_mut(4).unwrap().read(), One);
        assert_eq!(bit_str.get_mut(5).unwrap().read(), Zero);
        assert_eq!(bit_str.get_mut(6).unwrap().read(), Zero);
        assert_eq!(bit_str.get_mut(7).unwrap().read(), One);
        assert_eq!(bit_str.get_mut(8), None);
        assert_eq!(bit_str.get_mut(9), None);
        assert_eq!(bit_str.get_mut(10), None);

        assert_eq!(bit_str.get_mut(0).unwrap().write(Zero), One);
        assert_eq!(bit_str.get_mut(1).unwrap().write(One), One);
        assert_eq!(bit_str.get_mut(2).unwrap().write(Zero), Zero);
        assert_eq!(bit_str.get_mut(3).unwrap().write(One), Zero);
        bit_str.get_mut(4).unwrap().modify(Not::not);
        bit_str.get_mut(5).unwrap().modify(Not::not);
        bit_str.get_mut(6).unwrap().modify(identity);
        bit_str.get_mut(7).unwrap().modify(identity);

        assert_eq!(memory, [0b10101010]);
    }

    #[test]
    fn index() {
        let mut memory: [u8; 1] = [0b10010011];
        let bit_str = BitStr::new_mut(&mut memory);

        let bit_ref: &Bit = &bit_str[3];
        assert_eq!(bit_ref.read(), Zero);
        assert_eq!(bit_str[4].read(), One);

        let bit_mut: &mut Bit = &mut bit_str[3];
        assert_eq!(bit_mut.write(One), Zero);
        assert_eq!(bit_str[4].write(Zero), One);

        assert_eq!(memory, [0b10001011]);
    }

    #[test]
    fn eq() {
        let memory: [u8; 1] = [0b10010011];
        let bit_str = BitStr::new_ref(&memory);

        let memory_eq: [u8; 1] = [0b10010011];
        let bit_str_eq = BitStr::new_ref(&memory_eq);

        let memory_ne: [u8; 1] = [0b10000011];
        let bit_str_ne = BitStr::new_ref(&memory_ne);

        assert!(bit_str == bit_str);
        assert!(bit_str == bit_str_eq);
        assert!(bit_str != bit_str_ne);
    }
}
