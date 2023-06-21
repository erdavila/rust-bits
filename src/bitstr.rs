use std::fmt::{Binary, Debug, Display, LowerHex, UpperHex};
use std::ops::{
    Bound, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};
use std::ptr::NonNull;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::{Bit, BitValue, BitsPrimitive, Primitive};

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
        // TODO: review implementation. Calling read() requires decoding the just encoded reference.
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
        self.get_range_ref_repr(index..(index + 1))
    }

    /// Returns a subslice of this slice.
    ///
    /// `None` is returned if the range is out of bounds.
    #[inline]
    pub fn get_range_ref<R: RangeBounds<usize>>(&self, range: R) -> Option<&Self> {
        self.get_range_ref_repr(range)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    /// Returns a mutable subslice of this slice.
    ///
    /// `None` is returned if the range is out of bounds.
    #[inline]
    pub fn get_range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<&mut Self> {
        self.get_range_ref_repr(range)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    pub fn get_primitive<P: BitsPrimitive>(&self, first_bit_index: usize) -> Option<P> {
        // TODO: review implementation. Calling read() requires decoding the just encoded reference.
        self.get_primitive_ref(first_bit_index)
            .map(|p_ref| p_ref.read())
    }

    #[inline]
    pub fn get_primitive_ref<P: BitsPrimitive>(
        &self,
        first_bit_index: usize,
    ) -> Option<&Primitive<P>> {
        self.get_primitive_ref_repr::<P>(first_bit_index)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    pub fn get_primitive_mut<P: BitsPrimitive>(
        &mut self,
        first_bit_index: usize,
    ) -> Option<&mut Primitive<P>> {
        self.get_primitive_ref_repr::<P>(first_bit_index)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn get_primitive_ref_repr<P: BitsPrimitive>(&self, first_bit_index: usize) -> Option<RefRepr> {
        self.get_range_ref_repr(first_bit_index..(first_bit_index + P::BIT_COUNT))
    }

    #[inline]
    fn get_range_ref_repr<R: RangeBounds<usize>>(&self, range: R) -> Option<RefRepr> {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let mut components = repr.decode();

        let start = match range.start_bound() {
            Bound::Included(start) => *start,
            Bound::Excluded(start) => *start + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(end) => *end + 1,
            Bound::Excluded(end) => *end,
            Bound::Unbounded => components.metadata.bit_count,
        };

        (start <= end && end <= components.metadata.bit_count).then(|| {
            components.metadata.offset += start;
            components.metadata.bit_count = end - start;
            components.encode()
        })
    }
}

macro_rules! impl_index {
    ($type:ty, $output:ty, $method_ref:ident, $method_mut:ident, $error:literal) => {
        impl Index<$type> for BitStr {
            type Output = $output;
            #[inline]
            fn index(&self, index: $type) -> &Self::Output {
                self.$method_ref(index).expect($error)
            }
        }

        impl IndexMut<$type> for BitStr {
            #[inline]
            fn index_mut(&mut self, index: $type) -> &mut Self::Output {
                self.$method_mut(index).expect($error)
            }
        }
    };
}

macro_rules! impl_range_index {
    ($type:ty) => {
        impl_index!($type, BitStr, get_range_ref, get_range_mut, "invalid range");
    };
}

impl_index!(usize, Bit, get_ref, get_mut, "invalid index");
impl_range_index!(Range<usize>); // x..y
impl_range_index!(RangeInclusive<usize>); // x..=y
impl_range_index!(RangeToInclusive<usize>); // ..=y
impl_range_index!(RangeTo<usize>); // ..y
impl_range_index!(RangeFrom<usize>); // x..
impl_range_index!(RangeFull); // ..

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

impl<const N: usize> PartialEq<[BitValue; N]> for BitStr {
    #[inline]
    fn eq(&self, other: &[BitValue; N]) -> bool {
        PartialEq::<[BitValue]>::eq(self, other)
    }
}

impl PartialEq<[BitValue]> for BitStr {
    #[inline]
    fn eq(&self, other: &[BitValue]) -> bool {
        // TODO: optimize it

        for i in 0..self.len() {
            if self.get(i) != other.get(i).copied() {
                return false;
            }
        }

        true
    }
}

impl Display for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Binary::fmt(self, f)
    }
}

impl Binary for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: optimize it

        let mut bits = String::with_capacity(self.len());
        for i in (0..self.len()).rev() {
            bits.push(if self[i].read().to_bool() { '1' } else { '0' });
        }

        write!(f, "{}{bits}", if f.alternate() { "0b" } else { "" })
    }
}

impl LowerHex for BitStr {
    #[inline]
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl UpperHex for BitStr {
    #[inline]
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Debug for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{self}\"")
    }
}

#[cfg(test)]
mod tests {
    use std::convert::identity;
    use std::ops::Not;
    use std::ptr::NonNull;

    use crate::refrepr::RefRepr;
    use crate::BitValue::{One, Zero};
    use crate::{Bit, BitStr, BitsPrimitive, Primitive};

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
    fn get_range_ref() {
        let memory: [u16; 2] = [0b01011111_11101001, 0b10010111_11111010]; // In memory: 10010111_11111010__01011111_11101001
        let bit_str = BitStr::new_ref(memory.as_ref());

        let range1: Option<&BitStr> = bit_str.get_range_ref(0..4);
        let range2: Option<&BitStr> = bit_str.get_range_ref(14..18);
        let range3: Option<&BitStr> = bit_str.get_range_ref(28..32);
        let range_x: Option<&BitStr> = bit_str.get_range_ref(6..10);

        assert!(range1.is_some());
        assert!(range2.is_some());
        assert!(range3.is_some());
        assert!(range_x.is_some());
        assert_eq!(range1.unwrap().to_string(), "1001");
        assert_eq!(range2.unwrap().to_string(), "1001");
        assert_eq!(range3.unwrap().to_string(), "1001");
        assert_eq!(range_x.unwrap().to_string(), "1111");
        assert_eq!(range1, range1);
        assert_eq!(range1, range2);
        assert_eq!(range1, range3);
        assert_ne!(range1, range_x);
        assert!(bit_str.get_range_ref(28..33).is_none());
    }

    #[test]
    fn get_range_mut() {
        let mut memory: [u8; 1] = [0b10010011];
        let bit_str = BitStr::new_mut(&mut memory);

        let range: Option<&mut BitStr> = bit_str.get_range_mut(2..6);

        let range = range.unwrap();
        assert_eq!(range[0].write(One), Zero);
        assert_eq!(range[3].write(One), Zero);
        assert_eq!(memory, [0b10110111]);
    }

    #[test]
    fn get_range_forms() {
        let memory: [u8; 1] = [0b10010011];
        let bit_str = BitStr::new_ref(&memory);

        assert!(bit_str.get_range_ref(2..=5) == bit_str.get_range_ref(2..6));
        assert!(bit_str.get_range_ref(..=3) == bit_str.get_range_ref(0..4));
        assert!(bit_str.get_range_ref(..4) == bit_str.get_range_ref(0..4));
        assert!(bit_str.get_range_ref(4..) == bit_str.get_range_ref(4..8));
        assert!(bit_str.get_range_ref(..) == Some(bit_str));
    }

    #[test]
    fn get_primitive() {
        let mut memory: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: FEDCBA
        let bit_str = BitStr::new_mut(&mut memory);

        let value: Option<u16> = bit_str.get_primitive(4);
        assert_eq!(value.unwrap(), 0xEDCB);

        let u16_ref: Option<&Primitive<u16>> = bit_str.get_primitive_ref(4);
        assert_eq!(u16_ref.unwrap().read(), 0xEDCB);

        let u16_mut: Option<&mut Primitive<u16>> = bit_str.get_primitive_mut(4);
        assert_eq!(u16_mut.unwrap().write(0x1234), 0xEDCB);
        assert_eq!(memory, [0x4A, 0x23, 0xF1]); // In memory: F1234A

        // Test index limits
        let bit_str = BitStr::new_ref(&memory);
        assert!(bit_str.get_primitive::<u8>(16).is_some());
        assert!(bit_str.get_primitive::<u8>(17).is_none());
        assert!(bit_str.get_primitive::<u16>(8).is_some());
        assert!(bit_str.get_primitive::<u16>(9).is_none());
        assert!(bit_str.get_primitive::<u32>(0).is_none());
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

        let bit_str = BitStr::new_ref(&memory);
        let bit_substr: &BitStr = &bit_str[2..6];
        assert_eq!(bit_substr.len(), 4);
        assert_eq!(bit_substr, bit_str.get_range_ref(2..6).unwrap());
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

    #[test]
    fn eq_bit_values() {
        let memory: [u8; 1] = [0b10010011];
        let bit_str = BitStr::new_ref(&memory);
        let bit_substr = &bit_str[2..6];

        assert!(bit_str == &[One, One, Zero, Zero, One, Zero, Zero, One]);
        assert!(bit_substr == &[Zero, Zero, One, Zero]);
        assert!(bit_str == [One, One, Zero, Zero, One, Zero, Zero, One].as_ref());
        assert!(bit_substr == [Zero, Zero, One, Zero].as_ref());
    }

    #[test]
    fn formatting() {
        let memory: [u8; 2] = [0b00101011, 0b00001111];
        let bit_str = BitStr::new_ref(memory.as_ref());

        assert_eq!(format!("{bit_str}"), "0000111100101011");
        assert_eq!(format!("{bit_str:b}"), "0000111100101011");
        assert_eq!(format!("{bit_str:#b}"), "0b0000111100101011");
        // assert_eq!(format!("{bit_str:x}"), "0f2b");
        // assert_eq!(format!("{bit_str:#x}"), "0x0f2b");
        // assert_eq!(format!("{bit_str:X}"), "0F2B");
        // assert_eq!(format!("{bit_str:#X}"), "0x0F2B");
        assert_eq!(format!("{bit_str:?}"), "\"0000111100101011\"");
    }
}
