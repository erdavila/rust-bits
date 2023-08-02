use std::cmp::{self, Ordering};
use std::hash::Hash;
use std::ops::{
    Bound, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};

use crate::iter::{BitIterator, Iter, IterMut, IterRef, RawIter};
use crate::ref_encoding::bit_pointer::BitPointer;
use crate::ref_encoding::offset::Offset;
use crate::ref_encoding::{RefComponents, RefRepr};
use crate::utils::underlying_bytes_regions::UnderlyingBytesRegions;
use crate::utils::{BitPattern, CountedBits, Either};
use crate::{Bit, BitAccessor, BitString, BitValue, BitsPrimitive, Primitive, PrimitiveAccessor};

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
    pub fn new_ref(under: &[u8]) -> &Self {
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
    pub fn new_mut(under: &mut [u8]) -> &mut Self {
        let repr = Self::new_repr(under);
        unsafe { std::mem::transmute(repr) }
    }

    #[inline]
    fn new_repr(under: &[u8]) -> RefRepr {
        let components = RefComponents {
            bit_ptr: BitPointer::new_normalized(under.into(), 0),
            bit_count: under.len() * u8::BIT_COUNT,
        };
        components.encode()
    }

    /// Returns the number of referenced bits.
    #[inline]
    pub fn len(&self) -> usize {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        repr.decode().bit_count
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
        Self::on_range(
            index..(index + 1),
            self.ref_components(),
            |range_ref_components| {
                let accessor = BitAccessor::new(range_ref_components.bit_ptr);
                accessor.get()
            },
        )
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
        Self::on_range(
            first_bit_index..(first_bit_index + P::BIT_COUNT),
            self.ref_components(),
            |range_ref_components| {
                let accessor = PrimitiveAccessor::new(range_ref_components.bit_ptr);
                accessor.get()
            },
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
        let range = resolve_range(range, components.bit_count);
        Self::on_range(range, components, |range_ref_components| {
            range_ref_components.encode()
        })
    }

    #[inline]
    fn on_range<F, R>(range: Range<usize>, components: RefComponents, f: F) -> Option<R>
    where
        F: FnOnce(RefComponents) -> R,
    {
        (range.start <= range.end && range.end <= components.bit_count).then(|| {
            let range_ref_components = RefComponents {
                bit_ptr: components.bit_ptr.add_offset(range.start),
                bit_count: range.len(),
            };

            f(range_ref_components)
        })
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

        assert!(index <= components.bit_count, "invalid index");

        let lsb_components = RefComponents {
            bit_ptr: components.bit_ptr,
            bit_count: index,
        };
        let msb_components = RefComponents {
            bit_ptr: components.bit_ptr.add_offset(index),
            bit_count: components.bit_count - index,
        };

        (msb_components.encode(), lsb_components.encode())
    }

    #[inline]
    fn only_zeros(&self) -> bool {
        let components = self.ref_components();

        macro_rules! read_and_test {
            ($index:expr, $offset:expr, $bit_count:expr) => {{
                let byte = unsafe { components.bit_ptr.byte_ptr().add($index).read() };
                let mut bits = byte >> $offset.value();
                if $bit_count != u8::BIT_COUNT {
                    bits &= BitPattern::<u8>::new_with_zeros()
                        .and_ones($bit_count)
                        .get();
                }
                if bits != 0 {
                    return false;
                }
            }};
        }

        let regions =
            UnderlyingBytesRegions::new(components.bit_ptr.offset(), components.bit_count);

        match regions {
            UnderlyingBytesRegions::Multiple {
                lsb_byte,
                full_bytes,
                msb_byte,
            } => {
                if let Some(lsb) = lsb_byte {
                    read_and_test!(0, lsb.bit_offset, lsb.bit_count);
                }

                if let Some(full) = full_bytes {
                    for index in full.indexes {
                        read_and_test!(index, Offset::new(0), u8::BIT_COUNT);
                    }
                }

                if let Some(msb) = msb_byte {
                    read_and_test!(msb.index, Offset::new(0), msb.bit_count);
                }
            }
            UnderlyingBytesRegions::Single {
                bit_offset,
                bit_count,
            } => read_and_test!(0, bit_offset, bit_count),
        }

        true
    }

    #[inline]
    pub(crate) fn ref_components(&self) -> RefComponents {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        repr.decode()
    }

    #[inline]
    pub(crate) fn eq_slice(&self, other: &[BitValue]) -> bool {
        if self.len() != other.len() {
            return false;
        };

        let self_iter = self.iter();
        let mut other_iter = other.iter();

        let result = consume_iterator(
            self_iter,
            &mut other_iter,
            |other_iter, self_byte| {
                let mut other_bits = CountedBits::new();

                while other_bits.count < u8::BIT_COUNT {
                    other_bits.push_msb_value(*other_iter.next().unwrap());
                }

                let other_byte = other_bits.bits;
                (self_byte == other_byte).then_some(()).ok_or(())
            },
            |other_iter, self_bit| {
                let other_bit = other_iter.next().unwrap();
                (self_bit == *other_bit).then_some(()).ok_or(())
            },
        );

        result.is_ok()
    }

    #[inline]
    pub fn numeric_value(&self) -> NumericValue {
        NumericValue(self)
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

impl<'a> IntoIterator for &'a BitStr {
    type Item = &'a Bit;
    type IntoIter = IterRef<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_ref()
    }
}

fn consume_iterator<'a, I, State, FByte, FBit, Error>(
    mut iter: I,
    state: &mut State,
    mut consume_byte: FByte,
    mut consume_bit: FBit,
) -> Result<(), Error>
where
    I: BitIterator<'a>,
    FByte: FnMut(&mut State, I::PrimitiveItem<u8>) -> Result<(), Error>,
    FBit: FnMut(&mut State, I::Item) -> Result<(), Error>,
{
    while let Some(byte) = iter.next_primitive::<u8>() {
        consume_byte(state, byte)?;
    }

    for bit in iter {
        consume_bit(state, bit)?;
    }

    Ok(())
}

fn consume_iterator_pair<'left, 'right, ILeft, IRight, State, FByte, FBit, FIter, Error>(
    mut left_iter: ILeft,
    mut right_iter: IRight,
    state: &mut State,
    mut consume_byte_pair: FByte,
    mut consume_bit_pair: FBit,
    consume_non_depleted_iterator: FIter,
) -> Result<(), Error>
where
    ILeft: BitIterator<'left>,
    IRight: BitIterator<'right>,
    FByte:
        FnMut(&mut State, ILeft::PrimitiveItem<u8>, IRight::PrimitiveItem<u8>) -> Result<(), Error>,
    FBit: FnMut(&mut State, ILeft::Item, IRight::Item) -> Result<(), Error>,
    FIter: FnOnce(&mut State, Either<ILeft, IRight>) -> Result<(), Error>,
{
    while left_iter.len() >= u8::BIT_COUNT && right_iter.len() >= u8::BIT_COUNT {
        let (Some(left_byte), Some(right_byte)) = (left_iter.next_primitive::<u8>(), right_iter.next_primitive::<u8>()) else {
            unreachable!();
        };
        consume_byte_pair(state, left_byte, right_byte)?;
    }

    while left_iter.len() > 0 && right_iter.len() > 0 {
        let (Some(left_bit), Some(right_bit)) = (left_iter.next(), right_iter.next()) else {
            unreachable!();
        };
        consume_bit_pair(state, left_bit, right_bit)?;
    }

    if left_iter.len() > 0 {
        consume_non_depleted_iterator(state, Either::Left(left_iter))
    } else if right_iter.len() > 0 {
        consume_non_depleted_iterator(state, Either::Right(right_iter))
    } else {
        Ok(())
    }
}

impl PartialEq for BitStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        (self.len() == other.len()) && self.cmp(other) == Ordering::Equal
    }
}

impl<const N: usize> PartialEq<[BitValue; N]> for &BitStr {
    #[inline]
    fn eq(&self, other: &[BitValue; N]) -> bool {
        self.eq_slice(other)
    }
}

impl<const N: usize> PartialEq<[BitValue; N]> for &mut BitStr {
    #[inline]
    fn eq(&self, other: &[BitValue; N]) -> bool {
        self.eq_slice(other)
    }
}

impl<const N: usize> PartialEq<&BitStr> for [BitValue; N] {
    #[inline]
    fn eq(&self, other: &&BitStr) -> bool {
        *other == *self
    }
}

impl PartialEq<Vec<BitValue>> for &BitStr {
    #[inline]
    fn eq(&self, other: &Vec<BitValue>) -> bool {
        self.eq_slice(other)
    }
}

impl PartialEq<&BitStr> for Vec<BitValue> {
    #[inline]
    fn eq(&self, other: &&BitStr) -> bool {
        *other == *self
    }
}

impl Ord for BitStr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let left_iter = self.iter().reverse();
        let right_iter = other.iter().reverse();

        #[inline]
        fn cmp<T: Ord>(left: T, right: T) -> Result<(), Ordering> {
            let cmp = left.cmp(&right);
            if cmp != Ordering::Equal {
                Err(cmp)
            } else {
                Ok(())
            }
        }

        let result = consume_iterator_pair(
            left_iter,
            right_iter,
            &mut (),
            |_, left_byte, right_byte| cmp(left_byte, right_byte),
            |_, left_bit, right_bit| cmp(left_bit, right_bit),
            |_, iter| match iter {
                Either::Left(_) => Err(Ordering::Greater),
                Either::Right(_) => Err(Ordering::Less),
            },
        );

        result.err().unwrap_or(Ordering::Equal)
    }
}

impl PartialOrd for BitStr {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl PartialOrd<&mut BitStr> for &BitStr {
    #[inline]
    fn partial_cmp(&self, other: &&mut BitStr) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(*self, other))
    }
}

impl PartialOrd<&BitStr> for &mut BitStr {
    #[inline]
    fn partial_cmp(&self, other: &&BitStr) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(*self, other))
    }
}

impl Hash for BitStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let result: Result<_, ()> = consume_iterator(
            self.iter(),
            state,
            |state, byte| {
                byte.hash(state);
                Ok(())
            },
            |state, bit| {
                bit.hash(state);
                Ok(())
            },
        );
        result.unwrap();
    }
}

impl ToOwned for BitStr {
    type Owned = BitString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

#[derive(Eq)]
pub struct NumericValue<'a>(&'a BitStr);

impl<'a> NumericValue<'a> {
    #[inline]
    pub fn get_lower_bits_primitive<P: BitsPrimitive>(&self) -> P {
        let components = self.0.ref_components();

        let accessor = PrimitiveAccessor::new(components.bit_ptr);
        let bit_count = cmp::min(P::BIT_COUNT, components.bit_count);
        accessor.get_lower_bits(bit_count)
    }
}

impl<'a> PartialEq for NumericValue<'a> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<'a> Ord for NumericValue<'a> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let min_len = cmp::min(self.0.len(), other.0.len());

        let (self_extra, self_common) = self.0.split_at(min_len);
        let (other_extra, other_common) = other.0.split_at(min_len);

        if !self_extra.only_zeros() {
            Ordering::Greater
        } else if !other_extra.only_zeros() {
            Ordering::Less
        } else {
            self_common.cmp(other_common)
        }
    }
}

impl<'a> PartialOrd for NumericValue<'a> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use std::convert::identity;
    use std::ops::Not;

    use crate::ref_encoding::RefRepr;
    use crate::BitValue::{One, Zero};
    use crate::{Bit, BitStr, BitString, BitsPrimitive, Primitive};

    #[test]
    fn new_ref() {
        const N: usize = 3;
        let memory: [u8; N] = [0u8, 0u8, 0u8];

        let bit_str: &BitStr = BitStr::new_ref(&memory);

        assert_eq!(bit_str.len(), N * <u8>::BIT_COUNT);
        let components = unsafe { std::mem::transmute::<_, RefRepr>(bit_str) }.decode();
        assert_eq!(components.bit_ptr.byte_ptr(), memory.as_slice().into());
        assert_eq!(components.bit_ptr.offset().value(), 0);
        assert_eq!(components.bit_count, N * <u8>::BIT_COUNT);
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
        let memory: [u8; 4] = [0b11101001, 0b01011111, 0b11111010, 0b10010111]; // In memory: 10010111_11111010__01011111_11101001
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
        let memory: [u8; 6] = [0xEF, 0xCD, 0xAB, 0xEF, 0xCD, 0xAB]; // In memory: ABCDEFABCDEF
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

        let array = [
            Zero, One, Zero, Zero, One, Zero, One, One, Zero, Zero, One, One, Zero, Zero, Zero,
            One, One, Zero,
        ];
        let array_ne_1 = {
            let mut vals = array;
            vals[0] = !vals[0];
            vals
        };
        let array_ne_2 = {
            let mut vals = array;
            let last_index = vals.len() - 1;
            vals[last_index] = !vals[last_index];
            vals
        };

        assert!(bit_str == array);
        assert!(bit_str != array_ne_1);
        assert!(bit_str != array_ne_2);
        assert!(array == bit_str);
        assert!(array_ne_1 != bit_str);
        assert!(array_ne_2 != bit_str);

        assert!(bit_str == array.to_vec());
        assert!(bit_str != array_ne_1.to_vec());
        assert!(bit_str != array_ne_2.to_vec());
        assert!(array.to_vec() == bit_str);
        assert!(array_ne_1.to_vec() != bit_str);
        assert!(array_ne_2.to_vec() != bit_str);
    }

    #[test]
    fn ord() {
        let value: [u8; 3] = [0xBB, 0x00, 0xBB];
        let bit_str = BitStr::new_ref(&value); // In memory: BB00BB
        let empty = BitStr::new_mut(&mut []);
        let zero = &BitStr::new_ref(&[0u8])[..1];
        let one = &BitStr::new_ref(&[1u8])[..1];

        assert!(!(bit_str < bit_str));
        assert!(!(bit_str < BitStr::new_ref(&[0xBBu8, 0x00u8, 0xBBu8]))); // In memory: BB00BB (equal)
        assert!(bit_str < BitStr::new_ref(&[0xCCu8, 0x00u8, 0xBBu8])); // In memory: BB00CC (MSByte is equal but LSByte is larger)
        assert!(bit_str < BitStr::new_ref(&[0xAAu8, 0x00u8, 0xCCu8])); // In memory: CC00AA (MSByte is larger but LSByte is smaller)
        assert!(empty < zero); // "" < "0"
        assert!(zero > empty); // "0" > ""
        assert!(zero < one); // "0" < "1"
    }

    mod numeric_value {
        use crate::BitStr;

        #[test]
        fn cmp() {
            let bit_str_1 = &BitStr::new_ref(&[0b10010011u8, 0b0110u8])[0..12]; // In memory: 0110_10010011
            let bit_str_2 = BitStr::new_ref(&[0b10010011u8, 0b0110u8]); // In memory: 00000110_10010011
            let bit_str_3 = BitStr::new_ref(&[0b10010011u8, 0b0110u8, 0b0u8]); // In memory: 00000000_00000110_10010011
            let bit_str_4 = &BitStr::new_ref(&[0b10010011u8, 0b0110u8, 0b0u8])[0..20]; // In memory: 0000_00000110_10010011
            let bit_str_5 = &BitStr::new_ref(&[0b11000000u8, 0b10100100u8, 0b1u8])[6..22]; // In memory: 00000110_10010011
            let bit_str_ne_1 = BitStr::new_ref(&[0b10010011u8, 0b01000110u8]); // In memory: 01000110_10010011
            let bit_str_ne_2 = BitStr::new_ref(&[0b00010011u8, 0b00000110u8, 0b1u8]); // In memory: 00000001_00000110_10010011
            let bit_str_ne_3 =
                &BitStr::new_ref(&[0b00010011u8, 0b00000110u8, 0b00000000u8, 0b1u8])[..31]; // In memory: 00000001_00000000_00000110_10010011
            let bit_str_ne_4 = &BitStr::new_ref(&[0b10010011u8, 0b01000110u8])[..15]; // In memory: 1000110_10010011

            assert!(bit_str_1.numeric_value() == bit_str_1.numeric_value());
            assert!(bit_str_1.numeric_value() == bit_str_2.numeric_value());
            assert!(bit_str_1.numeric_value() == bit_str_3.numeric_value());
            assert!(bit_str_1.numeric_value() == bit_str_4.numeric_value());
            assert!(bit_str_1.numeric_value() == bit_str_5.numeric_value());

            assert!(bit_str_1.numeric_value() < bit_str_ne_1.numeric_value());
            assert!(bit_str_2.numeric_value() < bit_str_ne_1.numeric_value());
            assert!(bit_str_3.numeric_value() < bit_str_ne_1.numeric_value());
            assert!(bit_str_4.numeric_value() < bit_str_ne_1.numeric_value());
            assert!(bit_str_5.numeric_value() < bit_str_ne_1.numeric_value());

            assert!(bit_str_1.numeric_value() < bit_str_ne_2.numeric_value());
            assert!(bit_str_1.numeric_value() < bit_str_ne_3.numeric_value());
            assert!(bit_str_1.numeric_value() < bit_str_ne_4.numeric_value());

            assert!(bit_str_ne_1.numeric_value() > bit_str_1.numeric_value());
        }

        #[test]
        fn get_lower_bits_primitive() {
            let bit_str = &BitStr::new_ref(&[0b010011_10u8, 0b001100_10u8])[2..]; // In memory: 001100_10010011

            assert_eq!(
                bit_str.numeric_value().get_lower_bits_primitive::<u8>(),
                0b10010011u8
            );
            assert_eq!(
                bit_str[..4]
                    .numeric_value()
                    .get_lower_bits_primitive::<u8>(),
                0b00000011u8
            );
            assert_eq!(
                bit_str.numeric_value().get_lower_bits_primitive::<u16>(),
                0b00001100_10010011u16
            );
        }
    }

    #[test]
    fn to_owned() {
        let bit_str = &BitStr::new_ref(&[0b10010011u8])[1..7]; // In memory: 001001

        let bit_string: BitString = bit_str.to_owned();

        assert_eq!(bit_string, "001001".parse::<BitString>().unwrap());
    }
}
