use crate::PrimitiveType;

pub trait UnderlyingPrimitives {
    type Primitive: PrimitiveType;

    fn slice_ref(&self) -> &[Self::Primitive];
    fn bit_count(&self) -> usize;
}

impl<P: PrimitiveType> UnderlyingPrimitives for P {
    type Primitive = P;

    fn slice_ref(&self) -> &[Self::Primitive] {
        std::slice::from_ref(self)
    }

    fn bit_count(&self) -> usize {
        P::BIT_COUNT
    }
}

impl<P: PrimitiveType, const N: usize> UnderlyingPrimitives for [P; N] {
    type Primitive = P;

    fn slice_ref(&self) -> &[Self::Primitive] {
        self
    }

    fn bit_count(&self) -> usize {
        P::BIT_COUNT * N
    }
}

impl<P: PrimitiveType> UnderlyingPrimitives for [P] {
    type Primitive = P;

    fn slice_ref(&self) -> &[Self::Primitive] {
        self
    }

    fn bit_count(&self) -> usize {
        P::BIT_COUNT * self.len()
    }
}
