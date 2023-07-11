use std::fmt::{Binary, Debug, LowerHex, UpperHex};
use std::{cmp, mem};

use crate::refrepr::{Offset, TypedPointer};
use crate::{BitValue, BitsPrimitive};

// The number of bits required to represent a number of values.
//
// It is expected that `values_count` is a power of 2.
#[inline]
pub(crate) fn values_count_to_bit_count(values_count: usize) -> usize {
    values_count.trailing_zeros() as usize
}

// The number of values that can be represented with a number of bits.
#[inline]
pub(crate) fn bit_count_to_values_count(bit_count: usize) -> usize {
    1 << bit_count
}

#[inline]
pub(crate) fn max_value_for_bit_count(bit_count: usize) -> usize {
    bit_count_to_values_count(bit_count) - 1
}

#[inline]
pub(crate) fn required_elements_for_bit_count<P: BitsPrimitive>(bit_count: usize) -> usize {
    bit_count / P::BIT_COUNT + if bit_count % P::BIT_COUNT != 0 { 1 } else { 0 }
}

#[inline]
pub(crate) unsafe fn normalize_const_ptr_and_offset<P: BitsPrimitive>(
    ptr: *const P,
    offset: usize,
) -> (*const P, Offset<P>) {
    let index = offset / P::BIT_COUNT;
    let offset = Offset::new(offset);
    let ptr = ptr.add(index);
    (ptr, offset)
}

#[inline]
pub(crate) unsafe fn normalize_mut_ptr_and_offset<P: BitsPrimitive>(
    ptr: *mut P,
    offset: usize,
) -> (*mut P, Offset<P>) {
    let (ptr, offset) = normalize_const_ptr_and_offset(ptr as _, offset);
    (ptr as _, offset)
}

#[inline]
pub(crate) unsafe fn normalize_ptr_and_offset<P: BitsPrimitive>(
    ptr: TypedPointer<P>,
    offset: usize,
) -> (TypedPointer<P>, Offset<P>) {
    let (ptr, offset) = normalize_mut_ptr_and_offset(ptr.as_mut_ptr(), offset);
    (ptr.into(), offset)
}

#[derive(Clone, Copy, Default)]
pub(crate) struct CountedBits<P: BitsPrimitive> {
    pub(crate) bits: P,
    pub(crate) count: usize,
}

impl<P: BitsPrimitive> CountedBits<P> {
    pub(crate) fn new() -> Self {
        Self::with_count(P::ZERO, 0)
    }

    pub(crate) fn with_count(bits: P, count: usize) -> Self {
        Self { bits, count }
    }

    pub(crate) fn from_usize(bits: CountedBits<usize>) -> Self {
        debug_assert!(bits.count <= P::BIT_COUNT);
        Self::with_count(P::from_usize(bits.bits), bits.count)
    }

    pub(crate) fn to_usize(self) -> CountedBits<usize> {
        debug_assert!(self.count <= usize::BIT_COUNT);
        CountedBits::with_count(self.bits.to_usize(), self.count)
    }

    pub(crate) fn pop_lsb(&mut self, bit_count: usize) -> Self {
        let bit_count = cmp::min(bit_count, self.count);

        if bit_count == P::BIT_COUNT {
            mem::take(self)
        } else {
            let popped_bits = self.bits & BitPattern::new_with_zeros().and_ones(bit_count).get();
            self.drop_lsb(bit_count);
            Self::with_count(popped_bits, bit_count)
        }
    }

    pub(crate) fn push_msb(&mut self, bits: Self) {
        self.bits |= bits.bits << self.count;
        self.count += bits.count;
    }

    pub(crate) fn push_msb_value(&mut self, value: BitValue) {
        if value == BitValue::One {
            self.bits |= P::ONE << self.count;
        }
        self.count += 1;
    }

    pub(crate) fn drop_lsb(&mut self, bit_count: usize) {
        self.bits >>= bit_count;
        self.count -= bit_count;
    }

    pub(crate) fn room(&self) -> usize {
        P::BIT_COUNT - self.count
    }

    pub(crate) fn is_full(&self) -> bool {
        self.room() == 0
    }

    pub(crate) fn clear(&mut self) {
        *self = Self::new();
    }

    fn fmt(&self, f: &mut std::fmt::Formatter<'_>, format: char) -> std::fmt::Result {
        let formatted_bits = match format {
            'b' => format!("{:b}", self.bits),
            'x' => format!("{:x}", self.bits),
            _ => format!("{:X}", self.bits),
        };

        f.debug_struct("CountedBits")
            .field("bits", &formatted_bits)
            .field("count", &self.count)
            .field("BIT_COUNT", &P::BIT_COUNT)
            .finish()
    }
}

impl<P: BitsPrimitive> From<P> for CountedBits<P> {
    fn from(bits: P) -> Self {
        Self::with_count(bits, P::BIT_COUNT)
    }
}

impl<P: BitsPrimitive> UpperHex for CountedBits<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt(f, 'X')
    }
}

impl<P: BitsPrimitive> LowerHex for CountedBits<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt(f, 'x')
    }
}

impl<P: BitsPrimitive> Binary for CountedBits<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt(f, 'b')
    }
}

impl<P: BitsPrimitive> Debug for CountedBits<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        UpperHex::fmt(self, f)
    }
}

pub(crate) struct BitPattern<P: BitsPrimitive>(P);

impl<P: BitsPrimitive> BitPattern<P> {
    #[inline]
    pub(crate) fn new_with_zeros() -> Self {
        BitPattern(P::ZERO)
    }

    #[inline]
    pub(crate) fn new_with_ones() -> Self {
        Self::new_with_zeros().invert()
    }

    #[inline]
    pub(crate) fn and_zeros(self, bit_count: usize) -> Self {
        BitPattern(self.0 << bit_count)
    }

    #[inline]
    pub(crate) fn and_ones(self, bit_count: usize) -> Self {
        self.invert().and_zeros(bit_count).invert()
    }

    #[inline]
    pub(crate) fn invert(self) -> Self {
        BitPattern(!self.0)
    }

    #[inline]
    pub(crate) fn get(self) -> P {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::BitPattern;

    #[test]
    fn values_count_to_bit_count() {
        use super::values_count_to_bit_count;

        assert_eq!(values_count_to_bit_count(8), 3);
        assert_eq!(values_count_to_bit_count(16), 4);
        assert_eq!(values_count_to_bit_count(32), 5);
    }

    #[test]
    fn bit_count_to_values_count() {
        use super::bit_count_to_values_count;

        assert_eq!(bit_count_to_values_count(3), 8);
        assert_eq!(bit_count_to_values_count(4), 16);
        assert_eq!(bit_count_to_values_count(5), 32);
    }

    #[test]
    fn required_elements_for_bit_count() {
        use super::required_elements_for_bit_count;

        assert_eq!(required_elements_for_bit_count::<u8>(7), 1);
        assert_eq!(required_elements_for_bit_count::<u8>(8), 1);
        assert_eq!(required_elements_for_bit_count::<u8>(9), 2);
        assert_eq!(required_elements_for_bit_count::<u8>(16), 2);
        assert_eq!(required_elements_for_bit_count::<u8>(17), 3);
    }

    #[test]
    fn bit_pattern() {
        assert_eq!(BitPattern::<usize>::new_with_zeros().get(), 0b0000);
        assert_eq!(
            BitPattern::<usize>::new_with_zeros().and_ones(1).get(),
            0b00001
        );
        assert_eq!(
            BitPattern::<usize>::new_with_zeros()
                .and_ones(1)
                .and_zeros(2)
                .get(),
            0b0000100
        );
        assert_eq!(
            BitPattern::<usize>::new_with_zeros()
                .and_ones(1)
                .and_zeros(2)
                .and_ones(3)
                .get(),
            0b0000100111
        );

        assert_eq!(BitPattern::<usize>::new_with_ones().get(), !0b0000);
        assert_eq!(
            BitPattern::<usize>::new_with_ones().and_zeros(1).get(),
            !0b00001
        );
        assert_eq!(
            BitPattern::<usize>::new_with_ones()
                .and_zeros(1)
                .and_ones(2)
                .get(),
            !0b0000100
        );
        assert_eq!(
            BitPattern::<usize>::new_with_ones()
                .and_zeros(1)
                .and_ones(2)
                .and_zeros(3)
                .get(),
            !0b0000100111
        );

        assert_eq!(
            BitPattern::<usize>::new_with_zeros()
                .and_ones(1)
                .and_zeros(2)
                .invert()
                .get(),
            !0b0000100
        );
        assert_eq!(
            BitPattern::<usize>::new_with_ones()
                .and_zeros(1)
                .and_ones(2)
                .invert()
                .get(),
            0b0000100
        );
    }
}
