use crate::primitivetype::PrimitiveType;
use crate::UnderlyingPrimitives;

const DISCRIMINANT_MASK: usize = 0b0111;
const DISCRIMINANT_BIT_COUNT: usize = 3;

#[repr(C)]
pub(crate) struct DstRefRepr {
    ptr: *const (),
    metadata: usize,
}

impl DstRefRepr {
    pub(crate) fn new<U: UnderlyingPrimitives + ?Sized>(
        under: &U,
        offset: usize,
        bit_count: usize,
    ) -> Self {
        assert!(
            offset + bit_count <= under.bit_count(),
            "invalid bit offset"
        );

        let index = offset / U::Primitive::BIT_COUNT;
        let offset = offset % U::Primitive::BIT_COUNT;

        DstRefRepr {
            ptr: under.slice_ref()[index..].as_ptr().cast(),
            metadata: (offset << DISCRIMINANT_BIT_COUNT)
                | (U::Primitive::DISCRIMINANT & DISCRIMINANT_MASK),
        }
    }

    pub(crate) fn ptr<P: PrimitiveType>(&self) -> *const P {
        self.ptr as _
    }

    pub(crate) fn mut_ptr<P: PrimitiveType>(&self) -> *mut P {
        self.ptr as _
    }

    pub(crate) unsafe fn get_ref<'a, P: PrimitiveType>(&self) -> &'a P {
        &*(self.ptr as *const P)
    }

    pub(crate) unsafe fn get_mut<'a, P: PrimitiveType>(&self) -> &'a mut P {
        &mut *(self.ptr as *mut P)
    }

    pub(crate) fn discriminant(&self) -> usize {
        self.metadata & DISCRIMINANT_MASK
    }

    pub(crate) fn offset(&self) -> usize {
        self.metadata >> DISCRIMINANT_BIT_COUNT
    }
}
