use crate::utils::{max_value_for_bit_count, values_count_to_bit_count, BitPattern};
use crate::{BitsPrimitive, BitsPrimitiveDiscriminant, BitsPrimitiveSelector};

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
    ptr: UntypedPointer,
    pub(crate) metadata: EncodedMetadata,
}

impl RefRepr {
    fn encode<U: BitsPrimitive>(components: TypedRefComponents<U>) -> Self {
        fn untyped_encode(
            ptr: UntypedPointer,
            metadata: Metadata,
            bit_counts: ComponentsBitCounts,
        ) -> RefRepr {
            let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);
            assert!(
                metadata.bit_count <= max_bit_count,
                "bit_count too large for underlying type"
            );

            let metadata = metadata.encode(bit_counts.offset_bit_count);
            RefRepr { ptr, metadata }
        }

        let metadata = Metadata {
            underlying_primitive: U::DISCRIMINANT,
            offset: components.bit_ptr.offset().value(),
            bit_count: components.bit_count,
        };
        let bit_counts = ComponentsBitCounts::new::<U>();
        untyped_encode(
            components.bit_ptr.elem_ptr().as_untyped(),
            metadata,
            bit_counts,
        )
    }

    #[inline]
    pub(crate) fn decode(&self) -> UntypedRefComponents {
        UntypedRefComponents {
            ptr: self.ptr,
            metadata: self.metadata.decode(),
        }
    }
}

mod untyped_pointer {
    use std::ptr::NonNull;

    use crate::BitsPrimitive;

    use super::TypedPointer;

    #[repr(transparent)]
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub(crate) struct UntypedPointer(NonNull<()>);

    impl UntypedPointer {
        #[inline]
        pub(crate) fn ptr(&self) -> NonNull<()> {
            self.0
        }

        #[inline]
        pub(crate) fn as_typed<P: BitsPrimitive>(&self) -> TypedPointer<P> {
            (*self).into()
        }
    }

    impl From<NonNull<()>> for UntypedPointer {
        #[inline]
        fn from(ptr: NonNull<()>) -> Self {
            UntypedPointer(ptr)
        }
    }
}
pub(crate) use untyped_pointer::*;

mod typed_pointer {
    use std::ptr::NonNull;

    use crate::BitsPrimitive;

    use super::UntypedPointer;

    #[derive(Clone, Copy, Debug)]
    pub struct TypedPointer<P: BitsPrimitive>(NonNull<P>);

    impl<P: BitsPrimitive> TypedPointer<P> {
        #[inline]
        pub(crate) fn as_untyped(self) -> UntypedPointer {
            self.0.cast().into()
        }

        #[inline]
        pub(crate) unsafe fn read(self) -> P {
            self.0.as_ptr().read()
        }

        #[inline]
        pub(crate) unsafe fn write(self, value: P) {
            self.0.as_ptr().write(value);
        }

        #[inline]
        pub(crate) unsafe fn add(self, count: usize) -> Self {
            Self::from(self.0.as_ptr().add(count))
        }

        #[cfg(test)]
        #[inline]
        pub(crate) fn as_ptr(self) -> *const P {
            self.0.as_ptr()
        }

        #[inline]
        pub(crate) unsafe fn as_mut(&mut self) -> &mut P {
            self.0.as_mut()
        }
    }

    impl<P: BitsPrimitive> From<UntypedPointer> for TypedPointer<P> {
        #[inline]
        fn from(ptr: UntypedPointer) -> Self {
            TypedPointer(ptr.ptr().cast())
        }
    }

    impl<P: BitsPrimitive> From<&P> for TypedPointer<P> {
        #[inline]
        fn from(value: &P) -> Self {
            TypedPointer(NonNull::from(value))
        }
    }

    impl<P: BitsPrimitive> From<&mut P> for TypedPointer<P> {
        #[inline]
        fn from(value: &mut P) -> Self {
            TypedPointer(NonNull::from(value))
        }
    }

    impl<P: BitsPrimitive> From<&[P]> for TypedPointer<P> {
        #[inline]
        fn from(value: &[P]) -> Self {
            TypedPointer(NonNull::from(value).cast())
        }
    }

    impl<P: BitsPrimitive> From<&mut [P]> for TypedPointer<P> {
        #[inline]
        fn from(value: &mut [P]) -> Self {
            TypedPointer(NonNull::from(value).cast())
        }
    }

    impl<P: BitsPrimitive> From<*mut P> for TypedPointer<P> {
        #[inline]
        fn from(ptr: *mut P) -> Self {
            TypedPointer(unsafe { NonNull::new_unchecked(ptr) })
        }
    }
}
pub(crate) use typed_pointer::*;

mod offset {
    use std::marker::PhantomData;

    use crate::BitsPrimitive;

    #[derive(Clone, Copy, Debug)]
    pub(crate) struct Offset<P: BitsPrimitive> {
        value: usize,
        phantom: PhantomData<P>,
    }

    impl<P: BitsPrimitive> Offset<P> {
        #[inline]
        pub(crate) fn new(value: usize) -> Self {
            Offset {
                value: value % P::BIT_COUNT,
                phantom: PhantomData,
            }
        }

        #[inline]
        pub(crate) fn value(&self) -> usize {
            self.value
        }
    }
}
pub(crate) use offset::*;

mod bit_pointer {
    use crate::BitsPrimitive;

    use super::{Offset, TypedPointer};

    #[derive(Clone, Copy, Debug)]
    pub(crate) struct BitPointer<P: BitsPrimitive>(TypedPointer<P>, Offset<P>);

    impl<P: BitsPrimitive> BitPointer<P> {
        #[inline]
        pub(crate) fn new(ptr: TypedPointer<P>, offset: Offset<P>) -> Self {
            BitPointer(ptr, offset)
        }

        #[inline]
        pub(crate) fn new_normalized(ptr: TypedPointer<P>, offset: usize) -> Self {
            let index = offset / P::BIT_COUNT;
            let ptr = unsafe { ptr.add(index) };
            let offset = Offset::new(offset);
            Self::new(ptr, offset)
        }

        #[inline]
        pub(crate) fn elem_ptr(self) -> TypedPointer<P> {
            self.0
        }

        #[inline]
        pub(crate) fn set_elem_ptr(&mut self, elem_ptr: TypedPointer<P>) {
            self.0 = elem_ptr;
        }

        #[inline]
        pub(crate) fn offset(self) -> Offset<P> {
            self.1
        }

        #[inline]
        pub(crate) fn set_offset(&mut self, value: Offset<P>) {
            self.1 = value;
        }

        #[inline]
        pub(crate) fn add_offset(self, count: usize) -> Self {
            BitPointer::new_normalized(self.elem_ptr(), self.offset().value() + count)
        }
    }
}
pub(crate) use bit_pointer::*;

#[repr(transparent)]
pub(crate) struct EncodedMetadata(usize);

impl EncodedMetadata {
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
    pub(crate) underlying_primitive: BitsPrimitiveDiscriminant,
    pub(crate) offset: usize,
    pub(crate) bit_count: usize,
}

impl Metadata {
    fn encode(self, offset_bit_count: usize) -> EncodedMetadata {
        let mut metadata_bits = MetadataBits::from(self.bit_count);
        metadata_bits.push(self.offset, offset_bit_count);
        metadata_bits.push(
            encode_discriminant(self.underlying_primitive),
            DISCRIMINANT_BIT_COUNT,
        );
        EncodedMetadata(metadata_bits.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct UntypedRefComponents {
    pub(crate) ptr: UntypedPointer,
    pub(crate) metadata: Metadata,
}

impl UntypedRefComponents {
    #[inline]
    pub(crate) fn select<S: RefComponentsSelector>(self, selector: S) -> S::Output {
        struct PSelector<S: RefComponentsSelector> {
            selector: S,
            untyped_components: UntypedRefComponents,
        }

        impl<S: RefComponentsSelector> BitsPrimitiveSelector for PSelector<S> {
            type Output = S::Output;

            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                let elem_ptr = self.untyped_components.ptr.as_typed::<U>();
                let offset = self.untyped_components.metadata.offset;

                let components = TypedRefComponents {
                    bit_ptr: BitPointer::new_normalized(elem_ptr, offset),
                    bit_count: self.untyped_components.metadata.bit_count,
                };

                self.selector.select(components)
            }
        }

        self.metadata.underlying_primitive.select(PSelector {
            selector,
            untyped_components: self,
        })
    }
}

pub(crate) trait RefComponentsSelector {
    type Output;

    fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output;
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct TypedRefComponents<P: BitsPrimitive> {
    pub(crate) bit_ptr: BitPointer<P>,
    pub(crate) bit_count: usize,
}

impl<P: BitsPrimitive> TypedRefComponents<P> {
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

impl ComponentsBitCounts {
    #[inline]
    fn new<U: BitsPrimitive>() -> Self {
        Self::new_with_primitive_bit_count(U::BIT_COUNT)
    }

    #[inline]
    fn new_with_primitive_bit_count(primitive_bit_count: usize) -> Self {
        let offset_bit_count = values_count_to_bit_count(primitive_bit_count);
        let bit_count_bit_count = usize::BIT_COUNT - DISCRIMINANT_BIT_COUNT - offset_bit_count;

        ComponentsBitCounts {
            offset_bit_count,
            bit_count_bit_count,
        }
    }
}

impl From<BitsPrimitiveDiscriminant> for ComponentsBitCounts {
    #[inline]
    fn from(discr: BitsPrimitiveDiscriminant) -> Self {
        struct Selector;
        impl BitsPrimitiveSelector for Selector {
            type Output = usize;
            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                U::BIT_COUNT
            }
        }

        let primitive_bit_count = discr.select(Selector);
        Self::new_with_primitive_bit_count(primitive_bit_count)
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
        let mask = BitPattern::<usize>::new_with_zeros()
            .and_ones(bit_count)
            .get();
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

    use crate::refrepr::{
        encode_discriminant, BitPointer, EncodedMetadata, Offset, TypedRefComponents,
        DISCRIMINANT_BIT_COUNT,
    };
    use crate::utils::{max_value_for_bit_count, values_count_to_bit_count, BitPattern};
    use crate::BitsPrimitive;

    use super::{ComponentsBitCounts, ALL_DISCRIMINANTS};

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
        macro_rules! assert_conversions {
            ($type:ty, $under:ident, $offset:expr, $bit_count:expr) => {
                let original_components = TypedRefComponents {
                    bit_ptr: BitPointer::new($under.into(), Offset::new($offset)),
                    bit_count: $bit_count,
                };

                let repr = original_components.encode();
                let components = repr.decode();

                assert_eq!(
                    components.ptr,
                    original_components.bit_ptr.elem_ptr().as_untyped()
                );
                assert_eq!(
                    components.metadata.underlying_primitive,
                    <$type>::DISCRIMINANT
                );
                assert_eq!(
                    components.metadata.offset,
                    original_components.bit_ptr.offset().value()
                );
                assert_eq!(components.metadata.bit_count, original_components.bit_count);
            };
        }

        macro_rules! assert_conversions_for_type {
            ($type:ty) => {
                let under: &[$type] = fake_slice_large_enough_for_max_values();
                let bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);
                let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);

                assert_conversions!($type, under, 0, 0);
                assert_conversions!($type, under, 0, max_bit_count);
                assert_conversions!($type, under, max_offset, 0);
                assert_conversions!($type, under, max_offset, max_bit_count);
            };
        }

        assert_conversions_for_type!(usize);
        assert_conversions_for_type!(u8);
        assert_conversions_for_type!(u16);
        assert_conversions_for_type!(u32);
        assert_conversions_for_type!(u64);
        assert_conversions_for_type!(u128);
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

                assert_metadata_encoding!($type, BitPattern::<usize>::new_with_zeros().get(), 0, 0);
                assert_metadata_encoding!(
                    $type,
                    BitPattern::<usize>::new_with_ones().get(),
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

    macro_rules! test_bit_count_too_large {
        ($type:ty, $fn:ident) => {
            #[test]
            #[should_panic = "bit_count too large for underlying type"]
            fn $fn() {
                let under: $type = <$type>::ZERO;
                let bit_counts = ComponentsBitCounts::from(<$type>::DISCRIMINANT);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);

                let components = TypedRefComponents {
                    bit_ptr: BitPointer::new_normalized((&under).into(), 0),
                    bit_count: max_bit_count + 1,
                };

                components.encode();
            }
        };
    }

    test_bit_count_too_large!(usize, bit_count_too_large_for_usize);
    test_bit_count_too_large!(u8, bit_count_too_large_for_u8);
    test_bit_count_too_large!(u16, bit_count_too_large_for_u16);
    test_bit_count_too_large!(u32, bit_count_too_large_for_u32);
    test_bit_count_too_large!(u64, bit_count_too_large_for_u64);
    test_bit_count_too_large!(u128, bit_count_too_large_for_u128);

    #[test]
    fn pointer_and_offset_normalization() {
        macro_rules! assert_normalization {
            ($type:ty, $offset:expr, $expected_index:expr, $expected_offset:expr) => {
                let mut memory = [<$type>::ZERO, <$type>::ZERO, <$type>::ZERO];
                let under = &mut memory;
                let ptr = under.as_ref().into();

                let components = TypedRefComponents {
                    bit_ptr: BitPointer::new_normalized(ptr, $offset),
                    bit_count: 1,
                };

                assert_eq!(
                    components.bit_ptr.elem_ptr().as_ptr(),
                    unsafe { ptr.as_ptr().add($expected_index) }.cast()
                );
                assert_eq!(components.bit_ptr.offset().value(), $expected_offset);
            };
        }

        macro_rules! assert_normalization_for_type {
            ($type:ty) => {
                assert_normalization!($type, 0, 0, 0);
                assert_normalization!($type, <$type>::BIT_COUNT - 1, 0, <$type>::BIT_COUNT - 1);
                assert_normalization!($type, <$type>::BIT_COUNT, 1, 0);
                assert_normalization!($type, <$type>::BIT_COUNT + 1, 1, 1);
                assert_normalization!($type, 2 * <$type>::BIT_COUNT - 1, 1, <$type>::BIT_COUNT - 1);
                assert_normalization!($type, 2 * <$type>::BIT_COUNT, 2, 0);
                assert_normalization!($type, 2 * <$type>::BIT_COUNT + 1, 2, 1);
            };
        }

        assert_normalization_for_type!(usize);
        assert_normalization_for_type!(u8);
        assert_normalization_for_type!(u16);
        assert_normalization_for_type!(u32);
        assert_normalization_for_type!(u64);
        assert_normalization_for_type!(u128);
    }
}
