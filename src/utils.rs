use std::fmt::{Binary, Debug, LowerHex, UpperHex};
use std::{cmp, mem};

use crate::refrepr::Offset;
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
pub(crate) const fn bit_count_to_values_count(bit_count: usize) -> usize {
    1 << bit_count
}

#[inline]
pub(crate) const fn max_value_for_bit_count(bit_count: usize) -> usize {
    bit_count_to_values_count(bit_count) - 1
}

#[inline]
pub(crate) fn required_primitive_elements_typed<P: BitsPrimitive>(
    offset: Offset<P>,
    bit_count: usize,
) -> usize {
    required_primitive_elements_for_type::<P>(offset.value(), bit_count)
}

#[inline]
pub(crate) fn required_primitive_elements_for_type<P: BitsPrimitive>(
    offset: usize,
    bit_count: usize,
) -> usize {
    required_primitive_elements(offset, bit_count, P::BIT_COUNT)
}

#[inline]
pub(crate) fn required_primitive_elements(
    offset: usize,
    bit_count: usize,
    element_bit_count: usize,
) -> usize {
    if bit_count == 0 {
        0
    } else {
        let end_offset = offset + bit_count;
        end_offset / element_bit_count
            + if end_offset % element_bit_count != 0 {
                1
            } else {
                0
            }
    }
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

    pub(crate) fn push_lsb(&mut self, bits: Self) {
        self.bits <<= bits.count;
        self.bits |= bits.bits;
        self.count += bits.count;
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

pub(crate) mod primitive_elements_regions {
    use std::ops::Range;

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) struct LsbElement {
        pub(crate) bit_offset: usize,
        pub(crate) bit_count: usize,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) struct FullElements {
        pub(crate) indexes: Range<usize>,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) struct MsbElement {
        pub(crate) index: usize,
        pub(crate) bit_count: usize,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) enum PrimitiveElementsRegions {
        Multiple {
            lsb_element: Option<LsbElement>,
            full_elements: Option<FullElements>,
            msb_element: Option<MsbElement>,
        },
        Single {
            bit_offset: usize,
            bit_count: usize,
        },
    }

    impl PrimitiveElementsRegions {
        pub(crate) fn new(offset: usize, bit_count: usize, element_bit_count: usize) -> Self {
            if bit_count == 0 {
                Self::Multiple {
                    lsb_element: None,
                    full_elements: None,
                    msb_element: None,
                }
            } else {
                let start_offset = offset;
                let end_offset = start_offset + bit_count;

                if start_offset > 0 && end_offset < element_bit_count {
                    Self::Single {
                        bit_offset: start_offset,
                        bit_count,
                    }
                } else {
                    let lsb_element = (start_offset > 0).then_some(LsbElement {
                        bit_offset: start_offset,
                        bit_count: element_bit_count - start_offset,
                    });

                    let msb_elem_index = end_offset / element_bit_count;
                    let msb_elem_bit_count = end_offset % element_bit_count;
                    let msb_element = (msb_elem_bit_count > 0).then_some(MsbElement {
                        index: msb_elem_index,
                        bit_count: msb_elem_bit_count,
                    });

                    let full_elems_idxs_start = if lsb_element.is_some() { 1 } else { 0 };
                    let full_elems_idxs_end = msb_elem_index;
                    let full_elems_idxs_range = full_elems_idxs_start..full_elems_idxs_end;
                    let full_elements =
                        (!full_elems_idxs_range.is_empty()).then_some(FullElements {
                            indexes: full_elems_idxs_range,
                        });

                    Self::Multiple {
                        lsb_element,
                        full_elements,
                        msb_element,
                    }
                }
            }
        }
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

pub(crate) enum Either<L, R> {
    Left(L),
    Right(R),
}

#[cfg(test)]
mod tests {
    use crate::utils::BitPattern;
    use crate::BitsPrimitive;

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
    fn required_primitive_elements() {
        use super::required_primitive_elements;

        assert_eq!(required_primitive_elements(0, 0, u8::BIT_COUNT), 0);
        assert_eq!(required_primitive_elements(0, 1, u8::BIT_COUNT), 1);
        assert_eq!(required_primitive_elements(0, 8, u8::BIT_COUNT), 1);
        assert_eq!(required_primitive_elements(0, 9, u8::BIT_COUNT), 2);
        assert_eq!(required_primitive_elements(0, 16, u8::BIT_COUNT), 2);
        assert_eq!(required_primitive_elements(0, 17, u8::BIT_COUNT), 3);

        assert_eq!(required_primitive_elements(1, 0, u8::BIT_COUNT), 0);
        assert_eq!(required_primitive_elements(1, 1, u8::BIT_COUNT), 1);
        assert_eq!(required_primitive_elements(1, 7, u8::BIT_COUNT), 1);
        assert_eq!(required_primitive_elements(1, 8, u8::BIT_COUNT), 2);
        assert_eq!(required_primitive_elements(1, 15, u8::BIT_COUNT), 2);
        assert_eq!(required_primitive_elements(1, 16, u8::BIT_COUNT), 3);

        assert_eq!(required_primitive_elements(7, 0, u8::BIT_COUNT), 0);
        assert_eq!(required_primitive_elements(7, 1, u8::BIT_COUNT), 1);
        assert_eq!(required_primitive_elements(7, 2, u8::BIT_COUNT), 2);
        assert_eq!(required_primitive_elements(7, 9, u8::BIT_COUNT), 2);
        assert_eq!(required_primitive_elements(7, 10, u8::BIT_COUNT), 3);
    }

    #[test]
    fn primitive_elements_regions() {
        use super::primitive_elements_regions::*;

        // |--------|--------|--------[]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 0, 0),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: None,
                msb_element: None,
            }
        );

        // |--------|--------|---[#####]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 5, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: None,
                msb_element: Some(MsbElement {
                    index: 0,
                    bit_count: 5
                }),
            }
        );

        // |--------|--------|[########]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 8, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: Some(FullElements { indexes: 0..1 }),
                msb_element: None,
            }
        );

        // |--------|---[#####|########]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 13, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: Some(FullElements { indexes: 0..1 }),
                msb_element: Some(MsbElement {
                    index: 1,
                    bit_count: 5
                }),
            }
        );

        // |--------|[########|########]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 16, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: Some(FullElements { indexes: 0..2 }),
                msb_element: None,
            }
        );

        // |---[#####|########|########]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 21, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: Some(FullElements { indexes: 0..2 }),
                msb_element: Some(MsbElement {
                    index: 2,
                    bit_count: 5
                }),
            }
        );

        // |[########|########|########]|
        assert_eq!(
            PrimitiveElementsRegions::new(0, 24, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: Some(FullElements { indexes: 0..3 }),
                msb_element: None,
            }
        );

        // |--------|--------|-----[]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 0, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: None,
                full_elements: None,
                msb_element: None,
            }
        );

        // |--------|--------|---[##]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 2, 8),
            PrimitiveElementsRegions::Single {
                bit_offset: 3,
                bit_count: 2
            }
        );

        // |--------|--------|[#####]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 5, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: Some(LsbElement {
                    bit_offset: 3,
                    bit_count: 5
                }),
                full_elements: None,
                msb_element: None,
            }
        );

        // |--------|---[#####|#####]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 10, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: Some(LsbElement {
                    bit_offset: 3,
                    bit_count: 5
                }),
                full_elements: None,
                msb_element: Some(MsbElement {
                    index: 1,
                    bit_count: 5
                }),
            }
        );

        // |--------|[########|#####]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 13, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: Some(LsbElement {
                    bit_offset: 3,
                    bit_count: 5
                }),
                full_elements: Some(FullElements { indexes: 1..2 }),
                msb_element: None,
            }
        );

        // |---[#####|########|#####]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 18, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: Some(LsbElement {
                    bit_offset: 3,
                    bit_count: 5
                }),
                full_elements: Some(FullElements { indexes: 1..2 }),
                msb_element: Some(MsbElement {
                    index: 2,
                    bit_count: 5
                }),
            }
        );

        // |[########|########|#####]---|
        assert_eq!(
            PrimitiveElementsRegions::new(3, 21, 8),
            PrimitiveElementsRegions::Multiple {
                lsb_element: Some(LsbElement {
                    bit_offset: 3,
                    bit_count: 5
                }),
                full_elements: Some(FullElements { indexes: 1..3 }),
                msb_element: None,
            }
        );
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
