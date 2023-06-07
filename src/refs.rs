use std::marker::PhantomData;

use duplicate::duplicate_item;

use crate::primitivetype::PrimitiveType;
use crate::utils::make_bits_pattern;
use crate::{Discriminant, DiscriminantExecutor, UnderlyingPrimitives};

#[duplicate_item(
    DstRefRepr      ptr_mut  ref_mut;
    [DstRefRepr]    [*const] [&'a];
    [DstMutRefRepr] [*mut]   [&'a mut];
)]
#[repr(C)]
pub(crate) struct DstRefRepr<'a> {
    ptr: ptr_mut(),
    metadata: usize,
    phantom: PhantomData<ref_mut()>,
}

#[duplicate_item(
    [
        DstRefRepr           [DstRefRepr]
        DstRefReprExecutor   [DstRefReprExecutor]
        RefComponents        [RefComponents]
        UntypedRefComponents [UntypedRefComponents]
        ref_mut(type)        [&type]
        slice_ref            [slice_ref]
        as_ptr               [as_ptr]
    ]
    [
        DstRefRepr           [DstMutRefRepr]
        DstRefReprExecutor   [DstMutRefReprExecutor]
        UntypedRefComponents [UntypedMutRefComponents]
        RefComponents        [MutRefComponents]
        ref_mut(type)        [&mut type]
        slice_ref            [slice_mut]
        as_ptr               [as_mut_ptr]
    ]
)]
impl<'a> DstRefRepr<'a> {
    pub(crate) fn encode<U: UnderlyingPrimitives + ?Sized>(
        under: ref_mut([U]),
        offset: usize,
        bit_count: usize,
    ) -> Self {
        let EncodingValues { metadata, index } = encode(under, offset, bit_count);
        DstRefRepr {
            ptr: under.slice_ref()[index..].as_ptr().cast(),
            metadata,
            phantom: PhantomData,
        }
    }

    pub(crate) fn decode_and_execute<E: DstRefReprExecutor<'a>>(self, executor: E) -> E::Output {
        let DecodingValues {
            discriminant,
            offset,
            bit_count,
        } = decode(self.metadata);

        let untyped_components = UntypedRefComponents {
            ptr: self.ptr,
            offset,
            bit_count,
        };

        struct DiscrExecutor<E> {
            untyped_components: UntypedRefComponents,
            repr_executor: E,
        }
        impl<'b, E: DstRefReprExecutor<'b>> DiscriminantExecutor<'b> for DiscrExecutor<E> {
            type Output = E::Output;

            fn execute<U: PrimitiveType + 'b>(self) -> Self::Output {
                let components = RefComponents::<U> {
                    ptr: self.untyped_components.ptr.cast(),
                    offset: self.untyped_components.offset,
                    bit_count: self.untyped_components.bit_count,
                    phantom: PhantomData,
                };
                self.repr_executor.execute(components)
            }
        }

        discriminant.execute(DiscrExecutor {
            untyped_components,
            repr_executor: executor,
        })
    }
}

struct EncodingValues {
    metadata: usize,
    index: usize,
}

fn encode<U: UnderlyingPrimitives + ?Sized>(
    under: &U,
    offset: usize,
    bit_count: usize,
) -> EncodingValues {
    assert!(
        offset + bit_count <= under.bit_count(),
        "invalid bit offset"
    );

    let index = offset / U::Primitive::BIT_COUNT;
    let offset = offset % U::Primitive::BIT_COUNT;

    let bit_counts = bit_counts(U::Primitive::DISCRIMINANT);
    let mut metadata_bits = UsizeBits(bit_count);

    metadata_bits.push(offset, bit_counts.offset_bit_count);

    let discriminant_bits = discriminant_to_bits(U::Primitive::DISCRIMINANT);
    metadata_bits.push(discriminant_bits, Discriminant::BIT_COUNT);

    let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);
    assert!(bit_count <= max_bit_count, "bit count too large");

    EncodingValues {
        metadata: metadata_bits.0,
        index,
    }
}

struct DecodingValues {
    discriminant: Discriminant,
    offset: usize,
    bit_count: usize,
}

fn decode(metadata: usize) -> DecodingValues {
    let mut metadata_bits = UsizeBits(metadata);

    let discriminant_bits = metadata_bits.pop(Discriminant::BIT_COUNT);
    let discriminant = discriminant_from_bits(discriminant_bits);

    let offset = metadata_bits.pop(bit_counts(discriminant).offset_bit_count);

    let bit_count = metadata_bits.0;

    DecodingValues {
        discriminant,
        offset,
        bit_count,
    }
}

fn discriminant_from_bits(bits: usize) -> Discriminant {
    Discriminant::VALUES
        .iter()
        .cloned()
        .find(|d| discriminant_to_bits(*d) == bits)
        .unwrap()
}

fn discriminant_to_bits(discr: Discriminant) -> usize {
    discr as usize
}

struct BitCounts {
    offset_bit_count: usize,
    bit_count_bit_count: usize,
}

fn bit_counts(discriminant: Discriminant) -> BitCounts {
    struct Executor;
    impl DiscriminantExecutor<'_> for Executor {
        type Output = usize;
        fn execute<P: PrimitiveType>(self) -> Self::Output {
            P::BIT_COUNT
        }
    }
    let primitive_type_bit_count = discriminant.execute(Executor);

    let offset_bit_count = primitive_type_bit_count.trailing_zeros() as usize;
    let bit_count_bit_count = usize::BIT_COUNT - Discriminant::BIT_COUNT - offset_bit_count;

    BitCounts {
        offset_bit_count,
        bit_count_bit_count,
    }
}

fn max_value_for_bit_count(bit_count: usize) -> usize {
    2usize.pow(bit_count as u32) - 1
}

#[duplicate_item(
    RefComponents      ptr_mut(type) ref_mut(type);
    [RefComponents]    [*const type] [&'a type];
    [MutRefComponents] [*mut type]   [&'a mut type];
)]
pub(crate) struct RefComponents<'a, P: PrimitiveType> {
    pub(crate) ptr: ptr_mut([P]),
    pub(crate) offset: usize,
    pub(crate) bit_count: usize,
    phantom: PhantomData<ref_mut([()])>,
}

#[duplicate_item(
    RefComponents      ref_mut(type) ref_mut_lt(type);
    [RefComponents]    [&type]       [&'a type];
    [MutRefComponents] [&mut type]   [&'a mut type];
)]
impl<'a, P: PrimitiveType> RefComponents<'a, P> {
    #[allow(clippy::needless_arbitrary_self_type)]
    pub fn get_ref(self: ref_mut([Self])) -> ref_mut_lt([P]) {
        unsafe { ref_mut([*self.ptr]) }
    }
}

#[duplicate_item(
    DstRefReprExecutor      RefComponents;
    [DstRefReprExecutor]    [RefComponents];
    [DstMutRefReprExecutor] [MutRefComponents];
)]
pub(crate) trait DstRefReprExecutor<'a> {
    type Output;
    fn execute<U: PrimitiveType + 'a>(self, components: RefComponents<'a, U>) -> Self::Output;
}

#[duplicate_item(
    UntypedRefComponents      ptr_mut(type);
    [UntypedRefComponents]    [*const type];
    [UntypedMutRefComponents] [*mut type];
)]
pub(crate) struct UntypedRefComponents {
    ptr: ptr_mut([()]),
    offset: usize,
    bit_count: usize,
}

struct UsizeBits(usize);

impl UsizeBits {
    fn push(&mut self, value: usize, bit_count: usize) {
        self.0 <<= bit_count;
        self.0 |= value; // Warning: all bits of `value` are ORed, not only the `bit_count` lsb bits!
    }

    fn pop(&mut self, bit_count: usize) -> usize {
        let popped = self.0 & make_bits_pattern::<usize>([bit_count]);
        self.0 >>= bit_count;
        popped
    }
}

#[cfg(test)]
mod tests {
    use crate::refs::{
        bit_counts, max_value_for_bit_count, DstRefRepr, DstRefReprExecutor, RefComponents,
        UntypedRefComponents,
    };
    use crate::{Discriminant, PrimitiveType};

    #[test]
    fn offset_bit_count() {
        macro_rules! assert_offset_bit_count {
            ($type:ty) => {
                let max_offset = <$type>::BIT_COUNT - 1;
                let expected = max_offset.count_ones() as usize;

                let bit_counts = bit_counts(<$type>::DISCRIMINANT);

                assert_eq!(bit_counts.offset_bit_count, expected);
            };
        }

        assert_offset_bit_count!(usize);
        assert_offset_bit_count!(u8);
        assert_offset_bit_count!(u16);
        assert_offset_bit_count!(u32);
        assert_offset_bit_count!(u64);
        assert_offset_bit_count!(u128);
    }

    #[test]
    fn max_value() {
        assert_eq!(max_value_for_bit_count(1), 1);
        assert_eq!(max_value_for_bit_count(2), 3);
        assert_eq!(max_value_for_bit_count(3), 7);
        assert_eq!(max_value_for_bit_count(4), 15);
        assert_eq!(max_value_for_bit_count(5), 31);
    }

    // Warning: the returned slice must not be dereferenced because it does not really reference a large region of memory!
    fn fake_slice_large_enough_for_max_values<'a, P: PrimitiveType>() -> &'a [P] {
        let bit_counts = bit_counts(P::DISCRIMINANT);
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
            ($under:ident, $discriminant:expr, $offset:expr, $bit_count:expr) => {
                let repr = DstRefRepr::encode($under, $offset, $bit_count);
                let (components, discriminant) = repr.decode_and_execute(Executor);

                assert!(std::ptr::eq(components.ptr, $under.as_ptr().cast()));
                assert_eq!(discriminant, $discriminant);
                assert_eq!(components.offset, $offset);
                assert_eq!(components.bit_count, $bit_count);
            };
        }

        macro_rules! assert_type_conversions {
            ($type:ty) => {
                let under = fake_slice_large_enough_for_max_values::<$type>();
                let bit_counts = bit_counts(<$type>::DISCRIMINANT);
                let max_offset = max_value_for_bit_count(bit_counts.offset_bit_count);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);

                assert_conversions!(under, <$type>::DISCRIMINANT, 0, 0);
                assert_conversions!(under, <$type>::DISCRIMINANT, max_offset, 0);
                assert_conversions!(under, <$type>::DISCRIMINANT, 0, max_bit_count);
                assert_conversions!(under, <$type>::DISCRIMINANT, max_offset, max_bit_count);
            };
        }

        struct Executor;
        impl<'a> DstRefReprExecutor<'a> for Executor {
            type Output = (UntypedRefComponents, Discriminant);
            fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output {
                let components = UntypedRefComponents {
                    ptr: components.ptr.cast(),
                    offset: components.offset,
                    bit_count: components.bit_count,
                };
                (components, U::DISCRIMINANT)
            }
        }

        assert_type_conversions!(usize);
        assert_type_conversions!(u8);
        assert_type_conversions!(u16);
        assert_type_conversions!(u32);
        assert_type_conversions!(u64);
        assert_type_conversions!(u128);
    }

    #[test]
    fn discriminant_encoding() {
        let max_value = max_value_for_bit_count(Discriminant::BIT_COUNT);
        for d in Discriminant::VALUES {
            let value = d as usize;
            assert!(value <= max_value);
        }
    }

    macro_rules! test_bit_count_too_large {
        ($test_name: ident, $type:ty) => {
            #[test]
            #[should_panic(expected = "bit count too large")]
            fn $test_name() {
                let bit_counts = bit_counts(<$type>::DISCRIMINANT);
                let max_bit_count = max_value_for_bit_count(bit_counts.bit_count_bit_count);
                const EXCESS: usize = 1;

                let under = fake_slice_large_enough_for_max_values::<$type>();
                DstRefRepr::encode(under, 0, max_bit_count + EXCESS);
            }
        };
    }

    test_bit_count_too_large!(bit_count_too_large_usize, usize);
    test_bit_count_too_large!(bit_count_too_large_u8, u8);
    test_bit_count_too_large!(bit_count_too_large_u16, u16);
    test_bit_count_too_large!(bit_count_too_large_u32, u32);
    test_bit_count_too_large!(bit_count_too_large_u64, u64);
    test_bit_count_too_large!(bit_count_too_large_u128, u128);
}
