use std::ptr::NonNull;

use crate::bitvalue::BitValue;
use crate::refrepr::{RefRepr, UntypedRefComponents};
use crate::{BitsPrimitive, BitsPrimitiveSelector};

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
        struct Selector {
            components: UntypedRefComponents,
        }
        impl BitsPrimitiveSelector for Selector {
            type Output = BitValue;
            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                let accessor = BitAccessor::new(
                    self.components.ptr.cast::<U>(),
                    self.components.metadata.offset,
                );
                accessor.get()
            }
        }

        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);
        components
            .metadata
            .underlying_primitive
            .select(Selector { components })
    }

    /// Sets the value of the referenced bit.
    ///
    /// It returns the previous value.
    #[inline]
    pub fn write(&mut self, value: BitValue) -> BitValue {
        struct Selector {
            value: BitValue,
            components: UntypedRefComponents,
        }
        impl BitsPrimitiveSelector for Selector {
            type Output = BitValue;
            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                let mut accessor = BitAccessor::new(
                    self.components.ptr.cast::<U>(),
                    self.components.metadata.offset,
                );
                let previous_value = accessor.get();
                accessor.set(self.value);
                previous_value
            }
        }

        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);
        components
            .metadata
            .underlying_primitive
            .select(Selector { value, components })
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
        struct Selector<F: FnOnce(BitValue) -> BitValue> {
            f: F,
            components: UntypedRefComponents,
        }
        impl<F: FnOnce(BitValue) -> BitValue> BitsPrimitiveSelector for Selector<F> {
            type Output = ();
            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                let mut accessor = BitAccessor::new(
                    self.components.ptr.cast::<U>(),
                    self.components.metadata.offset,
                );
                let previous_value = accessor.get();
                let new_value = (self.f)(previous_value);
                accessor.set(new_value);
            }
        }

        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);
        components
            .metadata
            .underlying_primitive
            .select(Selector { f, components });
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
