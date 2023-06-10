use crate::refs::{DstMutRefRepr, DstRefRepr, DstRefReprExecutor, RefComponents};
use crate::UnderlyingPrimitives;

/// A reference to a fixed-size sequence of bits anywhere in underlying
/// [primitives].
///
/// [primitives]: crate::PrimitiveType
#[repr(C)]
pub struct BitStr {
    _unsized: [()],
}

impl BitStr {
    /// Creates a reference to the sequence of bits in the underlying primitives.
    pub fn new_ref<U: UnderlyingPrimitives + ?Sized>(under: &U) -> &Self {
        let repr = DstRefRepr::encode(under, 0, under.bit_count());
        unsafe { std::mem::transmute(repr) }
    }

    /// Creates a reference to the sequence of mutable bits in the underlying
    /// primitives.
    pub fn new_mut<U: UnderlyingPrimitives + ?Sized>(under: &mut U) -> &mut Self {
        let repr = DstMutRefRepr::encode(under, 0, under.bit_count());
        unsafe { std::mem::transmute(repr) }
    }

    /// Returns the number of referenced bits.
    pub fn len(&self) -> usize {
        struct Executor;
        impl DstRefReprExecutor for Executor {
            type Output = usize;
            fn execute<U: crate::PrimitiveType>(
                self,
                components: RefComponents<U>,
            ) -> Self::Output {
                components.bit_count
            }
        }
        self.repr().decode_and_execute(Executor)
    }

    /// Returns the same as `self.len() == 0`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn repr(&self) -> DstRefRepr {
        unsafe { std::mem::transmute(self) }
    }
}

#[cfg(test)]
mod tests {
    use crate::{BitStr, PrimitiveType};

    #[test]
    fn new_ref() {
        macro_rules! assert_len {
            ($type:ty) => {
                let under: $type = 1;
                let bit_str: &BitStr = BitStr::new_ref(&under);
                assert_eq!(bit_str.len(), <$type>::BIT_COUNT);

                let under: [$type; 3] = [1, 2, 3];
                let bit_str: &BitStr = BitStr::new_ref(&under);
                assert_eq!(bit_str.len(), <$type>::BIT_COUNT * 3);

                let under: &[$type] = &under;
                let bit_str: &BitStr = BitStr::new_ref(under);
                assert_eq!(bit_str.len(), <$type>::BIT_COUNT * 3);
            };
        }

        assert_len!(usize);
        assert_len!(u8);
        assert_len!(u16);
        assert_len!(u32);
        assert_len!(u64);
        assert_len!(u128);
    }
}
