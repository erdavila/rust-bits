use std::fmt::{Binary, Debug, Display, LowerHex, UpperHex};
use std::marker::PhantomData;
use std::ops::{
    Bound, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};
use std::ptr::NonNull;

use crate::refrepr::{RefComponentsSelector, RefRepr, TypedRefComponents, UntypedRefComponents};
use crate::{Bit, BitAccessor, BitValue, BitsPrimitive, Primitive, PrimitiveAccessor};

use self::iter::Iter;

mod iter;

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
        struct Selector;
        impl OnRangeSelector for Selector {
            type Output = BitValue;
            #[inline]
            fn select<U: BitsPrimitive>(
                self,
                range_ref_components: TypedRefComponents<U>,
            ) -> Self::Output {
                let accessor =
                    BitAccessor::new(range_ref_components.ptr, range_ref_components.offset);
                accessor.get()
            }
        }

        select_on_range(index..(index + 1), self.ref_components(), Selector)
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
        struct Selector<P>(PhantomData<P>);
        impl<P: BitsPrimitive> OnRangeSelector for Selector<P> {
            type Output = P;
            #[inline]
            fn select<U: BitsPrimitive>(
                self,
                range_ref_components: TypedRefComponents<U>,
            ) -> Self::Output {
                let accessor = PrimitiveAccessor::<P, U>::new(
                    range_ref_components.ptr,
                    range_ref_components.offset,
                );
                accessor.get()
            }
        }

        select_on_range(
            first_bit_index..(first_bit_index + P::BIT_COUNT),
            self.ref_components(),
            Selector(PhantomData),
        )
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
        let components = self.ref_components();
        let range = resolve_range(range, components.metadata.bit_count);

        struct Selector;
        impl OnRangeSelector for Selector {
            type Output = RefRepr;
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                components.encode()
            }
        }

        select_on_range(range, components, Selector)
    }

    #[inline]
    pub fn iter(&self) -> Iter {
        let components = self.ref_components();
        let metadata = components.metadata;
        Iter {
            ptr: components.ptr,
            underlying_primitive: metadata.underlying_primitive,
            start_offset: metadata.offset,
            end_offset: metadata.offset + metadata.bit_count,
            phantom: PhantomData,
        }
    }

    #[inline]
    fn ref_components(&self) -> UntypedRefComponents {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        repr.decode()
    }
}

#[inline]
fn resolve_range<R: RangeBounds<usize>>(range: R, len: usize) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(start) => *start,
        Bound::Excluded(start) => *start + 1,
        Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        Bound::Included(end) => *end + 1,
        Bound::Excluded(end) => *end,
        Bound::Unbounded => len,
    };

    start..end
}

#[inline]
fn select_on_range<S: OnRangeSelector>(
    range: Range<usize>,
    components: UntypedRefComponents,
    selector: S,
) -> Option<S::Output> {
    (range.start <= range.end && range.end <= components.metadata.bit_count).then(|| {
        struct InnerSelector<S> {
            range: Range<usize>,
            selector: S,
        }
        impl<S: OnRangeSelector> RefComponentsSelector for InnerSelector<S> {
            type Output = S::Output;

            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let components = TypedRefComponents::new_normalized(
                    components.ptr,
                    components.offset + self.range.start,
                    self.range.len(),
                );
                self.selector.select(components)
            }
        }

        components.select(InnerSelector { range, selector })
    })
}

trait OnRangeSelector {
    type Output;

    fn select<U: BitsPrimitive>(self, range_ref_components: TypedRefComponents<U>) -> Self::Output;
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

macro_rules! return_false_if_ne {
    ($e1:expr, $e2:expr) => {
        if $e1 != $e2 {
            return false;
        }
    };
}

impl PartialEq for BitStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        return_false_if_ne!(self.len(), other.len());

        let mut self_iter = self.iter();
        let mut other_iter = other.iter();

        macro_rules! compare_with {
            ($stmt:tt $($tt:tt)*) => {
                $stmt let (Some(self_value), Some(other_value)) = (self_iter. $($tt)*, other_iter. $($tt)*) {
                    return_false_if_ne!(self_value, other_value);
                }
            };
        }

        compare_with!(while next_primitive::<u128>());
        compare_with!(if next_primitive::<u64>());
        compare_with!(if next_primitive::<u32>());
        compare_with!(if next_primitive::<u16>());
        compare_with!(if next_primitive::<u8>());
        compare_with!(while next());

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
        return_false_if_ne!(self.len(), other.len());

        let mut self_iter = self.iter();
        let mut other_iter = other.iter();

        macro_rules! compare_primitives {
            ($stmt:tt, $type:ty) => {
                $stmt let Some(self_bits) = self_iter.next_primitive::<$type>() {
                    let mut other_bits = <$type>::ZERO;
                    for i in 0..<$type>::BIT_COUNT {
                        if let Some(&BitValue::One) = other_iter.next() {
                            other_bits |= 1 << i;
                        }
                    }

                    return_false_if_ne!(self_bits, other_bits);
                }
            };
        }

        compare_primitives!(while, u128);
        compare_primitives!(if, u64);
        compare_primitives!(if, u32);
        compare_primitives!(if, u16);
        compare_primitives!(if, u8);

        while let (Some(bit1), Some(bit2)) = (self_iter.next(), other_iter.next()) {
            return_false_if_ne!(bit1, *bit2);
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
        let memory: [u16; 3] = [0xCDEF, 0xEFAB, 0xABCD]; // In memory: ABCDEFABCDEF
        let bit_str = BitStr::new_ref(&memory);
        let bit_str_1 = &bit_str[8..20]; // In memory: BCD
        let bit_str_2 = &bit_str[32..44]; // In memory: BCD
        let bit_str_ne_1 = &bit_str[20..32]; // In memory: EFA
        let bit_str_ne_2 = &bit_str[8..21];
        let bit_str_ne_3 = &bit_str[8..19];

        assert!(bit_str_1 == bit_str_1);
        assert!(bit_str_1 == bit_str_2);
        assert!(bit_str_1 != bit_str_ne_1);
        assert!(bit_str_1 != bit_str_ne_2);
        assert!(bit_str_1 != bit_str_ne_3);
    }

    #[test]
    fn eq_bit_values() {
        let memory: [u8; 3] = [0b10010011, 0b01100110, 0b01101100]; // In memory: 01101100_01100110_10010011
        let bit_str = &BitStr::new_ref(&memory)[3..21]; // In memory: 01100_01100110_10010

        let bit_values = [
            Zero, One, Zero, Zero, One, Zero, One, One, Zero, Zero, One, One, Zero, Zero, Zero,
            One, One, Zero,
        ];
        let bit_values_ne_1 = {
            let mut vals = bit_values;
            vals[0] = !vals[0];
            vals
        };
        let bit_values_ne_2 = {
            let mut vals = bit_values;
            let last_index = vals.len() - 1;
            vals[last_index] = !vals[last_index];
            vals
        };

        assert!(bit_str == &bit_values);
        assert!(bit_str != &bit_values_ne_1);
        assert!(bit_str != &bit_values_ne_2);
        assert!(bit_str != &bit_values[1..]);
        assert!(bit_str != &bit_values[..(bit_values.len() - 1)]);
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
