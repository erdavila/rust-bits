use std::marker::PhantomData;

use duplicate::duplicate_item;

use crate::primitivetype::PrimitiveType;
use crate::UnderlyingPrimitives;

const DISCRIMINANT_BIT_COUNT: usize = 3;

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

    pub(crate) fn decode(self) -> UntypedRefComponents<'a> {
        let DecodingValues {
            discriminant,
            offset,
        } = decode(self.metadata);

        let ptr = self.ptr;

        UntypedRefComponents {
            ptr,
            discriminant,
            offset,
            phantom: PhantomData,
        }
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
    let discriminant = U::Primitive::DISCRIMINANT;

    EncodingValues {
        metadata: (offset << DISCRIMINANT_BIT_COUNT) | discriminant,
        index,
    }
}

struct DecodingValues {
    discriminant: usize,
    offset: usize,
}

fn decode(metadata: usize) -> DecodingValues {
    let discriminant = metadata & make_mask([DISCRIMINANT_BIT_COUNT]);
    let offset = metadata >> DISCRIMINANT_BIT_COUNT;

    DecodingValues {
        discriminant,
        offset,
    }
}

#[duplicate_item(
    UntypedRefComponents      ptr_mut(type) ref_mut(type);
    [UntypedRefComponents]    [*const type] [&'a type];
    [UntypedMutRefComponents] [*mut type]   [&'a mut type];
)]
pub(crate) struct UntypedRefComponents<'a> {
    pub(crate) ptr: ptr_mut([()]),
    pub(crate) discriminant: usize,
    pub(crate) offset: usize,
    phantom: PhantomData<ref_mut([()])>,
}

#[duplicate_item(
    UntypedRefComponents      ref_mut(type);
    [UntypedRefComponents]    [&type];
    [UntypedMutRefComponents] [&mut type];
)]
impl<'a> UntypedRefComponents<'a> {
    #[allow(clippy::needless_arbitrary_self_type)]
    pub fn get_ref<P: PrimitiveType>(self: ref_mut([Self])) -> ref_mut([P]) {
        unsafe { ref_mut([*self.ptr.cast()]) }
    }
}

fn make_mask<I: IntoIterator<Item = usize>>(blocks_len: I) -> usize {
    let mut mask = 0;
    let mut parity = false;

    for block_len in blocks_len {
        mask = !mask << block_len;
        parity = !parity;
    }

    if parity {
        mask = !mask;
    }

    mask
}

#[cfg(test)]
mod tests {
    use crate::refs::DstRefRepr;
    use crate::PrimitiveType;

    #[test]
    fn make_mask() {
        use super::make_mask;

        assert_eq!(make_mask([]), 0b0);
        assert_eq!(make_mask([2]), 0b011);
        assert_eq!(make_mask([2, 3]), 0b011000);
        assert_eq!(make_mask([2, 3, 4]), 0b0110001111);
    }

    #[test]
    fn encode_and_decode() {
        macro_rules! assert_conversions {
            ($under:ident, $discriminant:expr, $offset:expr) => {
                let repr = DstRefRepr::encode($under, $offset, 1);
                let components = repr.decode();

                assert!(std::ptr::eq(components.ptr, $under.as_ptr().cast()));
                assert_eq!(components.discriminant, $discriminant);
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

        assert_type_conversions!(usize);
        assert_type_conversions!(u8);
        assert_type_conversions!(u16);
        assert_type_conversions!(u32);
        assert_type_conversions!(u64);
        assert_type_conversions!(u128);
    }
}
