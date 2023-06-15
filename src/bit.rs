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
            let accessor = BitAccessor::new(ptr.cast::<U>(), offset);
            accessor.get()
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

    /// Sets the value of the referenced bit.
    ///
    /// It returns the previous value.
    #[inline]
    pub fn write(&mut self, value: BitValue) -> BitValue {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);

        fn set<U: BitsPrimitive>(ptr: NonNull<()>, offset: usize, value: BitValue) -> BitValue {
            let mut accessor = BitAccessor::new(ptr.cast::<U>(), offset);
            let previous_value = accessor.get();
            accessor.set(value);
            previous_value
        }

        match components.metadata.underlying_primitive {
            BitsPrimitiveDiscriminant::Usize => {
                set::<usize>(components.ptr, components.metadata.offset, value)
            }
            BitsPrimitiveDiscriminant::U8 => {
                set::<u8>(components.ptr, components.metadata.offset, value)
            }
            BitsPrimitiveDiscriminant::U16 => {
                set::<u16>(components.ptr, components.metadata.offset, value)
            }
            BitsPrimitiveDiscriminant::U32 => {
                set::<u32>(components.ptr, components.metadata.offset, value)
            }
            BitsPrimitiveDiscriminant::U64 => {
                set::<u64>(components.ptr, components.metadata.offset, value)
            }
            BitsPrimitiveDiscriminant::U128 => {
                set::<u128>(components.ptr, components.metadata.offset, value)
            }
        }
    }

    /// Allows retrieving and setting the bit value in a single operation.
    ///
    /// The passed closure receives the current value and must return the new value.
    ///
    /// # Example
    ///
    /// TODO
    #[inline]
    pub fn modify<F: FnOnce(BitValue) -> BitValue>(&mut self, f: F) {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);

        fn modify<U: BitsPrimitive, F: FnOnce(BitValue) -> BitValue>(
            ptr: NonNull<()>,
            offset: usize,
            f: F,
        ) {
            let mut accessor = BitAccessor::new(ptr.cast::<U>(), offset);
            let previous_value = accessor.get();
            let new_value = f(previous_value);
            accessor.set(new_value);
        }

        match components.metadata.underlying_primitive {
            BitsPrimitiveDiscriminant::Usize => {
                modify::<usize, F>(components.ptr, components.metadata.offset, f)
            }
            BitsPrimitiveDiscriminant::U8 => {
                modify::<u8, F>(components.ptr, components.metadata.offset, f)
            }
            BitsPrimitiveDiscriminant::U16 => {
                modify::<u16, F>(components.ptr, components.metadata.offset, f)
            }
            BitsPrimitiveDiscriminant::U32 => {
                modify::<u32, F>(components.ptr, components.metadata.offset, f)
            }
            BitsPrimitiveDiscriminant::U64 => {
                modify::<u64, F>(components.ptr, components.metadata.offset, f)
            }
            BitsPrimitiveDiscriminant::U128 => {
                modify::<u128, F>(components.ptr, components.metadata.offset, f)
            }
        }
    }
}

struct BitAccessor<P: BitsPrimitive> {
    ptr: NonNull<P>,
    mask: P,
}

impl<P: BitsPrimitive> BitAccessor<P> {
    #[inline]
    fn new(ptr: NonNull<P>, bit_index: usize) -> Self {
        BitAccessor {
            ptr,
            mask: P::ONE << bit_index,
        }
    }

    #[inline]
    fn get(&self) -> BitValue {
        BitValue::from((unsafe { *self.ptr.as_ref() } & self.mask) != P::ZERO)
    }

    #[inline]
    fn set(&mut self, value: BitValue) {
        let mut_ref = unsafe { self.ptr.as_mut() };

        match value {
            BitValue::Zero => *mut_ref &= !self.mask,
            BitValue::One => *mut_ref |= self.mask,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::identity;
    use std::ops::Not;
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

    #[test]
    fn write() {
        let under = 0b10010011u8;

        let new_mut = |bit_index| -> &mut Bit {
            let components = TypedRefComponents {
                ptr: NonNull::from(&under),
                offset: bit_index,
                bit_count: 1,
            };
            let repr = components.encode();
            unsafe { std::mem::transmute(repr) }
        };

        assert_eq!(new_mut(0).write(Zero), One);
        assert_eq!(new_mut(1).write(One), One);
        assert_eq!(new_mut(2).write(Zero), Zero);
        assert_eq!(new_mut(3).write(One), Zero);
        assert_eq!(under, 0b10011010);
    }

    #[test]
    fn modify() {
        let under = 0b10010011u8;

        let new_mut = |bit_index| -> &mut Bit {
            let components = TypedRefComponents {
                ptr: NonNull::from(&under),
                offset: bit_index,
                bit_count: 1,
            };
            let repr = components.encode();
            unsafe { std::mem::transmute(repr) }
        };

        new_mut(4).modify(Not::not);
        new_mut(5).modify(Not::not);
        new_mut(6).modify(identity);
        new_mut(7).modify(identity);

        assert_eq!(under, 0b10100011);
    }
}
