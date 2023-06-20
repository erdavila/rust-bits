use std::ptr::NonNull;

use crate::BitsPrimitive;

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
pub(crate) unsafe fn normalize_const_ptr_and_offset<P: BitsPrimitive>(
    ptr: *const P,
    offset: usize,
) -> (*const P, usize) {
    let index = offset / P::BIT_COUNT;
    let offset = offset % P::BIT_COUNT;
    let ptr = ptr.add(index);
    (ptr, offset)
}

#[inline]
pub(crate) unsafe fn normalize_mut_ptr_and_offset<P: BitsPrimitive>(
    ptr: *mut P,
    offset: usize,
) -> (*mut P, usize) {
    let (ptr, offset) = normalize_const_ptr_and_offset(ptr as _, offset);
    (ptr as _, offset)
}

#[inline]
pub(crate) unsafe fn normalize_ptr_and_offset<P: BitsPrimitive>(
    ptr: NonNull<P>,
    offset: usize,
) -> (NonNull<P>, usize) {
    let (ptr, offset) = normalize_mut_ptr_and_offset(ptr.as_ptr(), offset);
    (NonNull::new_unchecked(ptr), offset)
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
