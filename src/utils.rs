use std::fmt::{Binary, Debug, LowerHex, UpperHex};
use std::{cmp, mem};

use crate::ref_encoding::offset::Offset;
use crate::{BitValue, BitsPrimitive};

// The number of bits required to represent a number of values.
//
// It is expected that `values_count` is a power of 2.
#[cfg(test)]
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
pub(crate) fn required_bytes(offset: Offset, bit_count: usize) -> usize {
    if bit_count == 0 {
        0
    } else {
        let end_offset = offset.value() + bit_count;
        end_offset / u8::BIT_COUNT
            + if end_offset % u8::BIT_COUNT != 0 {
                1
            } else {
                0
            }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Default)]
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

    #[inline]
    pub(crate) fn from_u8(bits: CountedBits<u8>) -> Self {
        Self::with_count(P::from_u8(bits.bits), bits.count)
    }

    #[inline]
    pub(crate) fn to_u8(self) -> CountedBits<u8> {
        debug_assert!(self.count <= u8::BIT_COUNT);
        CountedBits::with_count(self.bits.to_u8(), self.count)
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

    #[inline]
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

    pub(crate) fn clear_uncounted_bits(&mut self) {
        if self.count < P::BIT_COUNT {
            self.bits &= BitPattern::new_with_zeros().and_ones(self.count).get();
        }
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

pub(crate) mod underlying_bytes_regions {
    use std::ops::Range;

    use crate::ref_encoding::offset::Offset;
    use crate::BitsPrimitive;

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) struct LsbByte {
        pub(crate) bit_offset: Offset,
        pub(crate) bit_count: usize,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) struct FullBytes {
        pub(crate) indexes: Range<usize>,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) struct MsbByte {
        pub(crate) index: usize,
        pub(crate) bit_count: usize,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub(crate) enum UnderlyingBytesRegions {
        Multiple {
            lsb_byte: Option<LsbByte>,
            full_bytes: Option<FullBytes>,
            msb_byte: Option<MsbByte>,
        },
        Single {
            bit_offset: Offset,
            bit_count: usize,
        },
    }

    impl UnderlyingBytesRegions {
        pub(crate) fn new(offset: Offset, bit_count: usize) -> Self {
            if bit_count == 0 {
                Self::Multiple {
                    lsb_byte: None,
                    full_bytes: None,
                    msb_byte: None,
                }
            } else {
                let start_offset = offset.value();
                let end_offset = start_offset + bit_count;

                if start_offset > 0 && end_offset < u8::BIT_COUNT {
                    Self::Single {
                        bit_offset: offset,
                        bit_count,
                    }
                } else {
                    let lsb_byte = (start_offset > 0).then_some(LsbByte {
                        bit_offset: offset,
                        bit_count: u8::BIT_COUNT - start_offset,
                    });

                    let msb_byte_index = end_offset / u8::BIT_COUNT;
                    let msb_byte_bit_count = end_offset % u8::BIT_COUNT;
                    let msb_byte = (msb_byte_bit_count > 0).then_some(MsbByte {
                        index: msb_byte_index,
                        bit_count: msb_byte_bit_count,
                    });

                    let full_bytes_idxs_start = if lsb_byte.is_some() { 1 } else { 0 };
                    let full_bytes_idxs_end = msb_byte_index;
                    let full_bytes_idxs_range = full_bytes_idxs_start..full_bytes_idxs_end;
                    let full_bytes = (!full_bytes_idxs_range.is_empty()).then_some(FullBytes {
                        indexes: full_bytes_idxs_range,
                    });

                    Self::Multiple {
                        lsb_byte,
                        full_bytes,
                        msb_byte,
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
    use crate::ref_encoding::offset::Offset;
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
    fn required_bytes() {
        use super::required_bytes;

        macro_rules! assert_required_bytes {
            ($offset:expr, $bit_count:expr, $expected:expr) => {
                assert_eq!(required_bytes(Offset::new($offset), $bit_count), $expected);
            };
        }

        assert_required_bytes!(0, 0, 0);
        assert_required_bytes!(0, 1, 1);
        assert_required_bytes!(0, 8, 1);
        assert_required_bytes!(0, 9, 2);
        assert_required_bytes!(0, 16, 2);
        assert_required_bytes!(0, 17, 3);

        assert_required_bytes!(1, 0, 0);
        assert_required_bytes!(1, 1, 1);
        assert_required_bytes!(1, 7, 1);
        assert_required_bytes!(1, 8, 2);
        assert_required_bytes!(1, 15, 2);
        assert_required_bytes!(1, 16, 3);

        assert_required_bytes!(7, 0, 0);
        assert_required_bytes!(7, 1, 1);
        assert_required_bytes!(7, 2, 2);
        assert_required_bytes!(7, 9, 2);
        assert_required_bytes!(7, 10, 3);
    }

    #[test]
    fn underlying_bytes_regions() {
        use super::underlying_bytes_regions::*;

        // |--------|--------|--------[]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 0),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: None,
                msb_byte: None,
            }
        );

        // |--------|--------|---[#####]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 5),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: None,
                msb_byte: Some(MsbByte {
                    index: 0,
                    bit_count: 5
                }),
            }
        );

        // |--------|--------|[########]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 8),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: Some(FullBytes { indexes: 0..1 }),
                msb_byte: None,
            }
        );

        // |--------|---[#####|########]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 13),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: Some(FullBytes { indexes: 0..1 }),
                msb_byte: Some(MsbByte {
                    index: 1,
                    bit_count: 5
                }),
            }
        );

        // |--------|[########|########]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 16),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: Some(FullBytes { indexes: 0..2 }),
                msb_byte: None,
            }
        );

        // |---[#####|########|########]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 21),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: Some(FullBytes { indexes: 0..2 }),
                msb_byte: Some(MsbByte {
                    index: 2,
                    bit_count: 5
                }),
            }
        );

        // |[########|########|########]|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(0), 24),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: Some(FullBytes { indexes: 0..3 }),
                msb_byte: None,
            }
        );

        // |--------|--------|-----[]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 0,),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: None,
                full_bytes: None,
                msb_byte: None,
            }
        );

        // |--------|--------|---[##]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 2,),
            UnderlyingBytesRegions::Single {
                bit_offset: Offset::new(3),
                bit_count: 2
            }
        );

        // |--------|--------|[#####]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 5,),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: Some(LsbByte {
                    bit_offset: Offset::new(3),
                    bit_count: 5
                }),
                full_bytes: None,
                msb_byte: None,
            }
        );

        // |--------|---[#####|#####]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 10),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: Some(LsbByte {
                    bit_offset: Offset::new(3),
                    bit_count: 5
                }),
                full_bytes: None,
                msb_byte: Some(MsbByte {
                    index: 1,
                    bit_count: 5
                }),
            }
        );

        // |--------|[########|#####]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 13),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: Some(LsbByte {
                    bit_offset: Offset::new(3),
                    bit_count: 5
                }),
                full_bytes: Some(FullBytes { indexes: 1..2 }),
                msb_byte: None,
            }
        );

        // |---[#####|########|#####]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 18),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: Some(LsbByte {
                    bit_offset: Offset::new(3),
                    bit_count: 5
                }),
                full_bytes: Some(FullBytes { indexes: 1..2 }),
                msb_byte: Some(MsbByte {
                    index: 2,
                    bit_count: 5
                }),
            }
        );

        // |[########|########|#####]---|
        assert_eq!(
            UnderlyingBytesRegions::new(Offset::new(3), 21),
            UnderlyingBytesRegions::Multiple {
                lsb_byte: Some(LsbByte {
                    bit_offset: Offset::new(3),
                    bit_count: 5
                }),
                full_bytes: Some(FullBytes { indexes: 1..3 }),
                msb_byte: None,
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
