use crate::primitivetype::PrimitiveType;

const DISCRIMINANT_MASK: usize = 0b0111;
const DISCRIMINANT_BIT_COUNT: usize = 3;

#[repr(C)]
pub(crate) struct DstRefRepr {
    ptr: *const (),
    metadata: usize,
}

impl DstRefRepr {
    pub(crate) fn new<P: PrimitiveType>(p: &[P], offset: usize, bit_count: usize) -> Self {
        assert!(
            offset + bit_count <= p.len() * P::BIT_COUNT,
            "invalid bit offset"
        );

        let index = offset / P::BIT_COUNT;
        let offset = offset % P::BIT_COUNT;

        DstRefRepr {
            ptr: ((&p[index]) as *const P).cast(),
            metadata: (offset << DISCRIMINANT_BIT_COUNT) | (P::DISCRIMINANT & DISCRIMINANT_MASK),
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
