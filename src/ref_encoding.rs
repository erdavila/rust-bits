#[cfg(test)]
use crate::utils::{max_value_for_bit_count, CountedBits};
#[cfg(test)]
use crate::BitsPrimitive;

#[cfg(test)]
use self::bit_pointer::BitPointer;
#[cfg(test)]
use self::byte_pointer::BytePointer;
#[cfg(test)]
use self::offset::Offset;

#[cfg(test)]
#[repr(C)]
struct RefRepr {
    ptr: BytePointer,
    metadata: EncodedMetadata,
}
#[cfg(test)]
impl RefRepr {
    #[inline]
    fn encode(components: RefComponents) -> Self {
        let metadata = Metadata {
            offset: components.bit_ptr.offset(),
            bit_count: components.bit_count,
        };
        let metadata = metadata.encode();
        RefRepr {
            ptr: components.bit_ptr.byte_ptr(),
            metadata,
        }
    }

    #[inline]
    fn decode(&self) -> RefComponents {
        let metadata = self.metadata.decode();
        RefComponents {
            bit_ptr: BitPointer::new(self.ptr, metadata.offset),
            bit_count: metadata.bit_count,
        }
    }
}

#[cfg(test)]
struct Metadata {
    offset: Offset,
    bit_count: usize,
}
#[cfg(test)]
impl Metadata {
    #[inline]
    fn encode(self) -> EncodedMetadata {
        let max_bit_count = EncodedMetadata::MAX_BIT_COUNT;
        assert!(self.bit_count <= max_bit_count, "bit_count too large");

        let mut bits = CountedBits::new();
        let mut push = |value, bit_count| {
            bits.push_lsb(CountedBits::with_count(value, bit_count));
        };

        push(self.bit_count, EncodedMetadata::BIT_COUNT_BIT_COUNT);
        push(self.offset.value(), EncodedMetadata::OFFSET_BIT_COUNT);

        EncodedMetadata(bits.bits)
    }
}

#[cfg(test)]
#[repr(transparent)]
struct EncodedMetadata(usize);
#[cfg(test)]
impl EncodedMetadata {
    const OFFSET_BIT_COUNT: usize = 3;
    const BIT_COUNT_BIT_COUNT: usize = usize::BIT_COUNT - Self::OFFSET_BIT_COUNT;

    const MAX_OFFSET: usize = max_value_for_bit_count(Self::OFFSET_BIT_COUNT);
    const MAX_BIT_COUNT: usize = max_value_for_bit_count(Self::BIT_COUNT_BIT_COUNT);

    #[inline]
    fn decode(&self) -> Metadata {
        let mut bits = CountedBits::from(self.0);
        let offset = bits.pop_lsb(EncodedMetadata::OFFSET_BIT_COUNT).bits;
        let bit_count = bits.pop_lsb(EncodedMetadata::BIT_COUNT_BIT_COUNT).bits;

        Metadata {
            offset: Offset::new(offset),
            bit_count,
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct RefComponents {
    bit_ptr: BitPointer,
    bit_count: usize,
}
#[cfg(test)]
impl RefComponents {
    #[inline]
    fn encode(self) -> RefRepr {
        RefRepr::encode(self)
    }
}

#[cfg(test)]
mod bit_pointer {
    use super::byte_pointer::BytePointer;
    use super::offset::Offset;

    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub(crate) struct BitPointer(BytePointer, Offset);

    impl BitPointer {
        #[inline]
        pub(crate) fn new(byte_ptr: BytePointer, offset: Offset) -> Self {
            BitPointer(byte_ptr, offset)
        }

        #[inline]
        pub(crate) fn byte_ptr(self) -> BytePointer {
            self.0
        }

        #[inline]
        pub(crate) fn offset(self) -> Offset {
            self.1
        }
    }
}

mod byte_pointer {
    use std::ptr::NonNull;

    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub(crate) struct BytePointer(NonNull<u8>);

    impl From<&[u8]> for BytePointer {
        #[inline]
        fn from(value: &[u8]) -> Self {
            BytePointer(NonNull::from(value).cast())
        }
    }

    impl From<&u8> for BytePointer {
        #[inline]
        fn from(value: &u8) -> Self {
            BytePointer(NonNull::from(value))
        }
    }
}

#[cfg(test)]
mod offset {
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub(crate) struct Offset(u8);

    impl Offset {
        #[inline]
        pub(crate) fn new(value: usize) -> Self {
            Offset((value & 0b0111) as u8)
        }

        #[inline]
        pub(crate) fn value(&self) -> usize {
            self.0 as usize
        }
    }
}

#[cfg(test)]
mod tests {
    use std::slice;

    use crate::ref_encoding::bit_pointer::BitPointer;
    use crate::ref_encoding::offset::Offset;
    use crate::ref_encoding::{EncodedMetadata, RefComponents};
    use crate::utils::{required_primitive_elements, BitPattern};
    use crate::BitsPrimitive;

    use super::byte_pointer::BytePointer;

    // Warning: the returned slice must not be dereferenced because it does not really reference a large region of memory!
    fn fake_slice_large_enough_for_max_values<'a>() -> &'a [u8] {
        let len = required_primitive_elements(
            EncodedMetadata::MAX_OFFSET,
            EncodedMetadata::MAX_BIT_COUNT,
            u8::BIT_COUNT,
        );
        unsafe { slice::from_raw_parts(&0u8, len) }
    }

    #[test]
    fn encode_and_decode() {
        macro_rules! assert_conversions {
            ($under:ident, $offset:expr, $bit_count:expr) => {
                let original_components = RefComponents {
                    bit_ptr: BitPointer::new($under.into(), Offset::new($offset)),
                    bit_count: $bit_count,
                };

                let repr = original_components.encode();
                let decoded_components = repr.decode();

                assert_eq!(decoded_components, original_components);
            };
        }

        let under = fake_slice_large_enough_for_max_values();

        assert_conversions!(under, 0, 0);
        assert_conversions!(under, 0, EncodedMetadata::MAX_BIT_COUNT);
        assert_conversions!(under, EncodedMetadata::MAX_OFFSET, 0);
        assert_conversions!(
            under,
            EncodedMetadata::MAX_OFFSET,
            EncodedMetadata::MAX_BIT_COUNT
        );
    }

    #[test]
    fn metadata_encoding_limits() {
        macro_rules! assert_metadata_encoding {
            ($offset_and_bit_count_bits:expr, $expected_offset:expr, $expected_bit_count:expr) => {
                let encoded_metadata = EncodedMetadata($offset_and_bit_count_bits);

                let metadata = encoded_metadata.decode();

                assert_eq!(metadata.offset.value(), $expected_offset);
                assert_eq!(metadata.bit_count, $expected_bit_count);
            };
        }
        assert_metadata_encoding!(BitPattern::<usize>::new_with_zeros().get(), 0, 0);
        assert_metadata_encoding!(
            BitPattern::<usize>::new_with_ones().get(),
            EncodedMetadata::MAX_OFFSET,
            EncodedMetadata::MAX_BIT_COUNT
        );
    }

    #[test]
    #[should_panic = "bit_count too large"]
    fn bit_count_too_large() {
        let under = 0u8;
        let components = RefComponents {
            bit_ptr: BitPointer::new(BytePointer::from(&under), Offset::new(0)),
            bit_count: EncodedMetadata::MAX_BIT_COUNT + 1,
        };

        components.encode();
    }
}
