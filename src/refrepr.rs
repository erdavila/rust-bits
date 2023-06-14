use std::ptr::NonNull;

use crate::utils::{max_value_for_bit_count, values_count_to_bit_count, BitPattern};
use crate::{BitsPrimitive, BitsPrimitiveDiscriminant};

const DISCRIMINANT_BIT_COUNT: usize = 3;
const ALL_DISCRIMINANTS: [BitsPrimitiveDiscriminant; 6] = [
    BitsPrimitiveDiscriminant::Usize,
    BitsPrimitiveDiscriminant::U8,
    BitsPrimitiveDiscriminant::U16,
    BitsPrimitiveDiscriminant::U32,
    BitsPrimitiveDiscriminant::U64,
    BitsPrimitiveDiscriminant::U128,
];

#[repr(C)]
pub(crate) struct RefRepr {
    ptr: NonNull<()>,
    pub(crate) metadata: EncodedMetadata,
}

impl RefRepr {
    #[inline]
    fn encode(components: UntypedRefComponents) -> Self {
        RefRepr {
            ptr: components.ptr,
            metadata: components.metadata.encode(),
        }
    }

    #[inline]
    pub(crate) fn decode(&self) -> UntypedRefComponents {
        UntypedRefComponents {
            ptr: self.ptr,
            metadata: self.metadata.decode(),
        }
    }
}

#[repr(transparent)]
pub(crate) struct EncodedMetadata(usize);

impl EncodedMetadata {
    fn encode(metadata: Metadata) -> Self {
        let bit_counts = ComponentsBitCounts::from(metadata.underlying_primitive);

        let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
        assert!(
            metadata.offset <= max_offset,
            "offset too large for underlying type"
        );

        let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);
        assert!(
            metadata.bit_count <= max_bit_count,
            "bit_count too large for underlying type"
        );

        let mut bits = MetadataBits::from(metadata.bit_count);
        bits.push(metadata.offset, bit_counts.offset_bit_count);
        bits.push(
            encode_discriminant(metadata.underlying_primitive),
            DISCRIMINANT_BIT_COUNT,
        );

        EncodedMetadata(bits.0)
    }

    pub(crate) fn decode(&self) -> Metadata {
        let mut metadata_bits = MetadataBits::from(self.0);

        let encoded_discriminant = metadata_bits.pop(DISCRIMINANT_BIT_COUNT);
        let discriminant = decode_discriminant(encoded_discriminant);
        let bit_counts = ComponentsBitCounts::from(discriminant);

        let offset = metadata_bits.pop(bit_counts.offset_bit_count);

        let bit_count = metadata_bits.0;

        Metadata {
            underlying_primitive: discriminant,
            offset,
            bit_count,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Metadata {
    underlying_primitive: BitsPrimitiveDiscriminant,
    offset: usize,
    pub(crate) bit_count: usize,
}

impl Metadata {
    #[inline]
    fn encode(self) -> EncodedMetadata {
        EncodedMetadata::encode(self)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct UntypedRefComponents {
    ptr: NonNull<()>,
    metadata: Metadata,
}

impl UntypedRefComponents {
    #[inline]
    pub(crate) fn encode(self) -> RefRepr {
        RefRepr::encode(self)
    }
}

#[derive(Debug)]
struct ComponentsBitCounts {
    offset_bit_count: usize,
    bit_count_bit_count: usize,
}

impl From<BitsPrimitiveDiscriminant> for ComponentsBitCounts {
    fn from(discr: BitsPrimitiveDiscriminant) -> Self {
        let primitive_bit_count = match discr {
            BitsPrimitiveDiscriminant::Usize => usize::BIT_COUNT,
            BitsPrimitiveDiscriminant::U8 => u8::BIT_COUNT,
            BitsPrimitiveDiscriminant::U16 => u16::BIT_COUNT,
            BitsPrimitiveDiscriminant::U32 => u32::BIT_COUNT,
            BitsPrimitiveDiscriminant::U64 => u64::BIT_COUNT,
            BitsPrimitiveDiscriminant::U128 => u128::BIT_COUNT,
        };

        let offset_bit_count = values_count_to_bit_count(primitive_bit_count);
        let bit_count_bit_count = usize::BIT_COUNT - DISCRIMINANT_BIT_COUNT - offset_bit_count;

        ComponentsBitCounts {
            offset_bit_count,
            bit_count_bit_count,
        }
    }
}

struct MetadataBits(usize);

impl MetadataBits {
    #[inline]
    fn push(&mut self, bits: usize, bit_count: usize) {
        self.0 = (self.0 << bit_count) | bits;
    }

    #[inline]
    fn pop(&mut self, bit_count: usize) -> usize {
        let mask = BitPattern::new_with_zeros().and_ones(bit_count).get();
        let popped = self.0 & mask;
        self.0 >>= bit_count;
        popped
    }
}

impl From<usize> for MetadataBits {
    #[inline]
    fn from(value: usize) -> Self {
        MetadataBits(value)
    }
}

#[inline]
fn encode_discriminant(discr: BitsPrimitiveDiscriminant) -> usize {
    discr as usize
}

#[inline]
fn decode_discriminant(bits: usize) -> BitsPrimitiveDiscriminant {
    ALL_DISCRIMINANTS
        .iter()
        .cloned()
        .find(|discr| encode_discriminant(*discr) == bits)
        .unwrap()
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::ptr::NonNull;

    use crate::refrepr::{
        encode_discriminant, ComponentsBitCounts, EncodedMetadata, Metadata, UntypedRefComponents,
        ALL_DISCRIMINANTS, DISCRIMINANT_BIT_COUNT,
    };
    use crate::utils::{max_value_for_bit_count, values_count_to_bit_count, BitPattern};
    use crate::BitsPrimitive;

    #[test]
    fn discriminant_encoding() {
        let max = max_value_for_bit_count(DISCRIMINANT_BIT_COUNT);
        for discr in ALL_DISCRIMINANTS {
            let bits = encode_discriminant(discr);
            assert!(bits <= max);
        }

        let set: HashSet<_> = ALL_DISCRIMINANTS
            .iter()
            .map(|d| encode_discriminant(*d))
            .collect();
        assert_eq!(
            set.len(),
            ALL_DISCRIMINANTS.len(),
            "the encoded value must be unique for every Discriminant"
        );
    }

    #[test]
    fn components_bit_counts() {
        macro_rules! assert_type {
            ($type:ty) => {
                let expected_offset_bit_count = values_count_to_bit_count(<$type>::BIT_COUNT);
                let expected_bit_count_bit_count =
                    usize::BIT_COUNT - DISCRIMINANT_BIT_COUNT - expected_offset_bit_count;

                let components_bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);

                assert_eq!(
                    components_bit_counts.offset_bit_count, expected_offset_bit_count,
                    "offset"
                );
                assert_eq!(
                    components_bit_counts.bit_count_bit_count, expected_bit_count_bit_count,
                    "bit_count"
                );
            };
        }

        assert_type!(usize);
        assert_type!(u8);
        assert_type!(u16);
        assert_type!(u32);
        assert_type!(u64);
        assert_type!(u128);
    }

    // Warning: the returned slice must not be dereferenced because it does not really reference a large region of memory!
    fn fake_slice_large_enough_for_max_values<'a, P: BitsPrimitive>() -> &'a [P] {
        let bit_counts = ComponentsBitCounts::from(P::DISCRIMINANT);
        let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
        let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);

        let under = P::ZERO;
        unsafe {
            std::slice::from_raw_parts(&under, (max_bit_count + max_offset) / P::BIT_COUNT + 1)
        }
    }

    #[test]
    fn encode_and_decode() {
        macro_rules! assert_convertions {
            ($type:ty, $under:ident, $offset:expr, $bit_count:expr) => {
                let original_components = UntypedRefComponents {
                    ptr: NonNull::from($under).cast(),
                    metadata: Metadata {
                        underlying_primitive: <$type>::DISCRIMINANT,
                        offset: $offset,
                        bit_count: $bit_count,
                    },
                };

                let repr = original_components.encode();
                let components = repr.decode();

                assert_eq!(components, original_components);
            };
        }

        macro_rules! assert_convertions_for_type {
            ($type:ty) => {
                let under: &[u8] = fake_slice_large_enough_for_max_values();
                let bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);
                let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);

                assert_convertions!($type, under, 0, 0);
                assert_convertions!($type, under, 0, max_bit_count);
                assert_convertions!($type, under, max_offset, 0);
                assert_convertions!($type, under, max_offset, max_bit_count);
            };
        }

        assert_convertions_for_type!(usize);
        assert_convertions_for_type!(u8);
        assert_convertions_for_type!(u16);
        assert_convertions_for_type!(u32);
        assert_convertions_for_type!(u64);
        assert_convertions_for_type!(u128);
    }

    #[test]
    fn metadata_encoding_limits() {
        macro_rules! assert_metadata_encoding {
            ($type:ty, $offset_and_bit_count_bits:expr, $expected_offset:expr, $expected_bit_count:expr) => {
                let encoded_metadata = EncodedMetadata(
                    ($offset_and_bit_count_bits << DISCRIMINANT_BIT_COUNT)
                        | encode_discriminant(<$type>::DISCRIMINANT),
                );

                let metadata = encoded_metadata.decode();

                assert_eq!(metadata.underlying_primitive, <$type>::DISCRIMINANT);
                assert_eq!(metadata.offset, $expected_offset);
                assert_eq!(metadata.bit_count, $expected_bit_count);
            };
        }

        macro_rules! assert_metadata_encoding_limits_for_type {
            ($type:ty) => {
                let bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);
                let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);

                assert_metadata_encoding!($type, BitPattern::new_with_zeros().get(), 0, 0);
                assert_metadata_encoding!(
                    $type,
                    BitPattern::new_with_ones().get(),
                    max_offset,
                    max_bit_count
                );
            };
        }

        assert_metadata_encoding_limits_for_type!(usize);
        assert_metadata_encoding_limits_for_type!(u8);
        assert_metadata_encoding_limits_for_type!(u16);
        assert_metadata_encoding_limits_for_type!(u32);
        assert_metadata_encoding_limits_for_type!(u64);
        assert_metadata_encoding_limits_for_type!(u128);
    }

    macro_rules! test_offset_too_large_for_type {
        ($type:ty, $fn:ident) => {
            #[test]
            #[should_panic = "offset too large for underlying type"]
            fn $fn() {
                let bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);
                let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
                let metadata = Metadata {
                    underlying_primitive: <$type>::DISCRIMINANT,
                    offset: max_offset + 1,
                    bit_count: 0,
                };

                metadata.encode();
            }
        };
    }

    test_offset_too_large_for_type!(usize, offset_too_large_for_usize);
    test_offset_too_large_for_type!(u8, offset_too_large_for_u8);
    test_offset_too_large_for_type!(u16, offset_too_large_for_u16);
    test_offset_too_large_for_type!(u32, offset_too_large_for_u32);
    test_offset_too_large_for_type!(u64, offset_too_large_for_u64);
    test_offset_too_large_for_type!(u128, offset_too_large_for_u128);

    macro_rules! test_bit_count_too_large_for_type {
        ($type:ty, $fn:ident) => {
            #[test]
            #[should_panic = "bit_count too large for underlying type"]
            fn $fn() {
                let bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);
                let metadata = Metadata {
                    underlying_primitive: <$type>::DISCRIMINANT,
                    offset: 0,
                    bit_count: max_bit_count + 1,
                };

                metadata.encode();
            }
        };
    }

    test_bit_count_too_large_for_type!(usize, bit_count_too_large_for_usize);
    test_bit_count_too_large_for_type!(u8, bit_count_too_large_for_u8);
    test_bit_count_too_large_for_type!(u16, bit_count_too_large_for_u16);
    test_bit_count_too_large_for_type!(u32, bit_count_too_large_for_u32);
    test_bit_count_too_large_for_type!(u64, bit_count_too_large_for_u64);
    test_bit_count_too_large_for_type!(u128, bit_count_too_large_for_u128);
}
