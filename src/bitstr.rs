use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{
    Bound, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};
use std::ptr::NonNull;

use crate::iter::{BitIterator, Iter, IterMut, IterRef, RawIter};
use crate::refrepr::{RefComponentsSelector, RefRepr, TypedRefComponents, UntypedRefComponents};
use crate::{Bit, BitAccessor, BitValue, BitsPrimitive, Primitive, PrimitiveAccessor};

mod fmt;

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
        Iter(RawIter::from(self.ref_components()))
    }

    #[inline]
    pub fn iter_ref(&self) -> IterRef {
        IterRef(RawIter::from(self.ref_components()))
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut {
        IterMut(RawIter::from(self.ref_components()))
    }

    #[inline]
    pub fn split_at(&self, index: usize) -> (&BitStr, &BitStr) {
        let (msb_repr, lsb_repr) = self.split_at_repr(index);
        unsafe { (std::mem::transmute(msb_repr), std::mem::transmute(lsb_repr)) }
    }

    #[inline]
    pub fn split_at_mut(&mut self, index: usize) -> (&mut BitStr, &mut BitStr) {
        let (msb_repr, lsb_repr) = self.split_at_repr(index);
        unsafe { (std::mem::transmute(msb_repr), std::mem::transmute(lsb_repr)) }
    }

    #[inline]
    fn split_at_repr(&self, index: usize) -> (RefRepr, RefRepr) {
        let components = self.ref_components();

        assert!(index <= components.metadata.bit_count, "invalid index");

        components.select({
            struct Selector(usize);
            impl RefComponentsSelector for Selector {
                type Output = (RefRepr, RefRepr);
                #[inline]
                fn select<U: BitsPrimitive>(
                    self,
                    components: TypedRefComponents<U>,
                ) -> Self::Output {
                    let lsb_components = TypedRefComponents::new_normalized(
                        components.ptr,
                        components.offset,
                        self.0,
                    );
                    let msb_components = TypedRefComponents::new_normalized(
                        components.ptr,
                        components.offset + self.0,
                        components.bit_count - self.0,
                    );
                    (msb_components.encode(), lsb_components.encode())
                }
            }

            Selector(index)
        })
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

trait ConsumeIterator<'a> {
    fn consume_primitive<P: BitsPrimitive + 'a>(&mut self, value: P) -> Result<(), ()>;
    fn consume_remainder_bit(&mut self, value: BitValue) -> Result<(), ()>;

    fn consume_iterator(&mut self, mut iter: Iter) -> Result<(), ()> {
        macro_rules! consume {
            ($stmt:tt, $type:ty) => {
                $stmt let Some(value) = iter.next_primitive::<$type>() {
                    self.consume_primitive(value)?;
                }
            };
        }

        consume!(while, u128);
        consume!(if, u64);
        consume!(if, u32);
        consume!(if, u16);
        consume!(if, u8);

        for value in iter {
            self.consume_remainder_bit(value)?;
        }

        Ok(())
    }
}

impl PartialEq for BitStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        };

        struct Consumer<'a> {
            other_iter: Iter<'a>,
        }
        impl<'a> ConsumeIterator<'a> for Consumer<'a> {
            #[inline]
            fn consume_primitive<P: BitsPrimitive + 'a>(
                &mut self,
                self_value: P,
            ) -> Result<(), ()> {
                let other_value = self.other_iter.next_primitive::<P>().unwrap();
                (self_value == other_value).then_some(()).ok_or(())
            }

            #[inline]
            fn consume_remainder_bit(&mut self, self_value: BitValue) -> Result<(), ()> {
                let other_value = self.other_iter.next().unwrap();
                (self_value == other_value).then_some(()).ok_or(())
            }
        }

        let self_iter = self.iter();
        let other_iter = other.iter();

        let mut consumer = Consumer { other_iter };
        consumer.consume_iterator(self_iter).is_ok()
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
        if self.len() != other.len() {
            return false;
        };

        struct Consumer<'a> {
            other_iter: std::slice::Iter<'a, BitValue>,
        }
        impl<'a> ConsumeIterator<'a> for Consumer<'a> {
            #[inline]
            fn consume_primitive<P: BitsPrimitive>(&mut self, self_bits: P) -> Result<(), ()> {
                let mut other_bits = P::ZERO;

                for i in 0..P::BIT_COUNT {
                    if let Some(BitValue::One) = self.other_iter.next() {
                        other_bits |= P::ONE << i;
                    }
                }

                (self_bits == other_bits).then_some(()).ok_or(())
            }

            #[inline]
            fn consume_remainder_bit(&mut self, self_value: BitValue) -> Result<(), ()> {
                let other_value = self.other_iter.next().unwrap();
                (self_value == *other_value).then_some(()).ok_or(())
            }
        }

        let self_iter = self.iter();
        let other_iter = other.iter();

        let mut consumer = Consumer { other_iter };
        consumer.consume_iterator(self_iter).is_ok()
    }
}

impl Hash for BitStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        struct Consumer<'a, H> {
            state: &'a mut H,
        }
        impl<'a, H: std::hash::Hasher> ConsumeIterator<'a> for Consumer<'a, H> {
            #[inline]
            fn consume_primitive<P: BitsPrimitive>(&mut self, value: P) -> Result<(), ()> {
                value.hash(self.state);
                Ok(())
            }

            #[inline]
            fn consume_remainder_bit(&mut self, value: BitValue) -> Result<(), ()> {
                value.hash(self.state);
                Ok(())
            }
        }

        let mut consumer = Consumer { state };
        consumer.consume_iterator(self.iter()).unwrap();
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
    fn split_at() {
        let memory: [u8; 2] = [0b10010011, 0b01101100];
        let bit_str = &BitStr::new_ref(&memory)[1..15];

        let (msb, lsb) = bit_str.split_at(6);
        assert_eq!(msb, &bit_str[6..]);
        assert_eq!(lsb, &bit_str[..6]);

        let (msb, lsb) = bit_str.split_at(0);
        assert_eq!(msb, &bit_str[0..]);
        assert_eq!(lsb, &bit_str[..0]);

        let (msb, lsb) = bit_str.split_at(14);
        assert_eq!(msb, &bit_str[14..]);
        assert_eq!(lsb, &bit_str[..14]);
    }

    #[test]
    #[should_panic = "invalid index"]
    fn split_at_panic() {
        let memory: [u8; 2] = [0b10010011, 0b01101100];
        let bit_str = &BitStr::new_ref(&memory)[1..15];

        bit_str.split_at(15);
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
}
