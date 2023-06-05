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

    pub(crate) fn decode_and_execute<E: DstRefReprExecutor>(self, executor: E) -> E::Output {
        let DecodingValues {
            discriminant,
            offset,
        } = decode(self.metadata);

        let untyped_components = UntypedRefComponents {
            ptr: self.ptr,
            offset,
        };

        struct DiscrExecutor<E> {
            untyped_components: UntypedRefComponents,
            repr_executor: E,
        }
        impl<E: DstRefReprExecutor> DiscriminantExecutor for DiscrExecutor<E> {
            type Output = E::Output;

            fn execute<U: PrimitiveType>(self) -> Self::Output {
                let components = RefComponents::<U> {
                    ptr: self.untyped_components.ptr.cast(),
                    offset: self.untyped_components.offset,
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

    let discriminant_bits = discriminant_to_bits(U::Primitive::DISCRIMINANT);

    EncodingValues {
        metadata: (offset << Discriminant::BIT_COUNT) | discriminant_bits,
        index,
    }
}

struct DecodingValues {
    discriminant: Discriminant,
    offset: usize,
}

fn decode(metadata: usize) -> DecodingValues {
    let discriminant_bits = metadata & make_bits_pattern::<usize>([Discriminant::BIT_COUNT]);
    let discriminant = discriminant_from_bits(discriminant_bits);

    let offset = metadata >> Discriminant::BIT_COUNT;

    DecodingValues {
        discriminant,
        offset,
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

#[duplicate_item(
    RefComponents      ptr_mut(type) ref_mut(type);
    [RefComponents]    [*const type] [&'a type];
    [MutRefComponents] [*mut type]   [&'a mut type];
)]
pub(crate) struct RefComponents<'a, P: PrimitiveType> {
    pub(crate) ptr: ptr_mut([P]),
    pub(crate) offset: usize,
    phantom: PhantomData<ref_mut([()])>,
}

#[duplicate_item(
    RefComponents      ref_mut(type);
    [RefComponents]    [&type];
    [MutRefComponents] [&mut type];
)]
impl<'a, P: PrimitiveType> RefComponents<'a, P> {
    #[allow(clippy::needless_arbitrary_self_type)]
    pub fn get_ref(self: ref_mut([Self])) -> ref_mut([P]) {
        unsafe { ref_mut([*self.ptr]) }
    }
}

#[duplicate_item(
    DstRefReprExecutor      RefComponents;
    [DstRefReprExecutor]    [RefComponents];
    [DstMutRefReprExecutor] [MutRefComponents];
)]
pub(crate) trait DstRefReprExecutor {
    type Output;
    fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output;
}

#[duplicate_item(
    UntypedRefComponents      ptr_mut(type);
    [UntypedRefComponents]    [*const type];
    [UntypedMutRefComponents] [*mut type];
)]
pub(crate) struct UntypedRefComponents {
    ptr: ptr_mut([()]),
    offset: usize,
}

#[cfg(test)]
mod tests {
    use crate::refs::{DstRefRepr, DstRefReprExecutor, RefComponents, UntypedRefComponents};
    use crate::{Discriminant, PrimitiveType};

    #[test]
    fn encode_and_decode() {
        macro_rules! assert_conversions {
            ($under:ident, $discriminant:expr, $offset:expr) => {
                let repr = DstRefRepr::encode($under, $offset, 1);
                let (components, discriminant) = repr.decode_and_execute(Executor);

                assert!(std::ptr::eq(components.ptr, $under.as_ptr().cast()));
                assert_eq!(discriminant, $discriminant);
                assert_eq!(components.offset, $offset);
            };
        }

        macro_rules! assert_type_conversions {
            ($type:ty) => {
                let under: &[$type] = &[0, 1];

                assert_conversions!(under, <$type>::DISCRIMINANT, 0);
                assert_conversions!(under, <$type>::DISCRIMINANT, 7);
            };
        }

        struct Executor;
        impl DstRefReprExecutor for Executor {
            type Output = (UntypedRefComponents, Discriminant);
            fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output {
                let components = UntypedRefComponents {
                    ptr: components.ptr.cast(),
                    offset: components.offset,
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
        let max_value = 2usize.pow(Discriminant::BIT_COUNT as u32) - 1;
        for d in Discriminant::VALUES {
            let value = d as usize;
            assert!(value <= max_value);
        }
    }
}
