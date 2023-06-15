use std::ptr::NonNull;

use crate::bitvalue::BitValue;
use crate::refrepr::RefRepr;
use crate::{BitsPrimitive, BitsPrimitiveDiscriminant};

/// Representation of a reference to a single bit in a [underlying memory].
///
/// The bit cannot be directly dereferenced. Instead, it must be read with the
/// [`read`] method and changed with the [`write`] and [`modify`] methods.
///
/// TODO: how to obtain a reference
///
/// # Example
///
/// TODO
///
/// [underlying memory]: crate::UnderlyingMemory
/// [`read`]: Bit::read
/// [`write`]: Bit::write
/// [`modify`]: Bit::modify
#[repr(C)]
pub struct Bit {
    _unsized: [()],
}

impl Bit {
    /// Gets the value of the referenced bit.
    #[inline]
    pub fn read(&self) -> BitValue {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);

        fn get<U: BitsPrimitive>(ptr: NonNull<()>, offset: usize) -> BitValue {
            let ptr = ptr.cast::<U>();
            let value = unsafe { *ptr.as_ref() };
            BitValue::from(((value >> offset) & U::ONE) == U::ONE)
        }

        match components.metadata.underlying_primitive {
            BitsPrimitiveDiscriminant::Usize => {
                get::<usize>(components.ptr, components.metadata.offset)
            }
            BitsPrimitiveDiscriminant::U8 => get::<u8>(components.ptr, components.metadata.offset),
            BitsPrimitiveDiscriminant::U16 => {
                get::<u16>(components.ptr, components.metadata.offset)
            }
            BitsPrimitiveDiscriminant::U32 => {
                get::<u32>(components.ptr, components.metadata.offset)
            }
            BitsPrimitiveDiscriminant::U64 => {
                get::<u64>(components.ptr, components.metadata.offset)
            }
            BitsPrimitiveDiscriminant::U128 => {
                get::<u128>(components.ptr, components.metadata.offset)
            }
        }
    }

    pub fn write(&mut self, value: BitValue) -> BitValue {
        todo!()
    }

    pub fn modify<F: FnOnce(BitValue) -> BitValue>(&mut self, f: F) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use std::ptr::NonNull;

    use crate::refrepr::TypedRefComponents;
    use crate::Bit;
    use crate::BitValue::{One, Zero};

    #[test]
    fn read() {
        let under = 0b10010011u8;

        let new_ref = |bit_index| -> &Bit {
            let components = TypedRefComponents {
                ptr: NonNull::from(&under),
                offset: bit_index,
                bit_count: 1,
            };
            let repr = components.encode();
            unsafe { std::mem::transmute(repr) }
        };

        assert_eq!(new_ref(0).read(), One);
        assert_eq!(new_ref(1).read(), One);
        assert_eq!(new_ref(2).read(), Zero);
        assert_eq!(new_ref(3).read(), Zero);
        assert_eq!(new_ref(4).read(), One);
        assert_eq!(new_ref(5).read(), Zero);
        assert_eq!(new_ref(6).read(), Zero);
        assert_eq!(new_ref(7).read(), One);
    }
}
