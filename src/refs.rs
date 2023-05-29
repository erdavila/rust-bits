use crate::primitivetype::{PrimitiveType, DISCRIMINANT_BIT_COUNT, DISCRIMINANT_MASK};

#[repr(C)]
pub(crate) struct DstRefParts {
    pub(crate) ptr: *const (),
    metadata: usize,
}

impl DstRefParts {
    pub(crate) fn new<P: PrimitiveType>(ptr: *const P, bit_index: usize) -> Self {
        DstRefParts {
            ptr: ptr as _,
            metadata: (bit_index << DISCRIMINANT_BIT_COUNT) | (P::DISCRIMINANT & DISCRIMINANT_MASK),
        }
    }

    pub(crate) fn discriminant(&self) -> usize {
        self.metadata & DISCRIMINANT_MASK
    }

    pub(crate) fn bit_index(&self) -> usize {
        self.metadata >> DISCRIMINANT_BIT_COUNT
    }
}
