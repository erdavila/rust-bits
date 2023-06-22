use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::copy_bits::copy_bits_raw;
use crate::refrepr::{RefComponentsSelector, RefRepr, TypedRefComponents, UntypedRefComponents};
use crate::BitsPrimitive;

#[repr(C)]
pub struct Primitive<P: BitsPrimitive> {
    _phantom: PhantomData<P>,
    _unsized: [()],
}

impl<P: BitsPrimitive> Primitive<P> {
    #[inline]
    pub fn read(&self) -> P {
        struct Selector<P>(PhantomData<P>);
        impl<P: BitsPrimitive> RefComponentsSelector for Selector<P> {
            type Output = P;
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let accessor = PrimitiveAccessor::<P, _>::new(components.ptr, components.offset);
                accessor.get()
            }
        }

        self.components().select(Selector::<P>(PhantomData))
    }

    #[inline]
    pub fn write(&mut self, value: P) -> P {
        struct Selector<P> {
            value: P,
        }
        impl<P: BitsPrimitive> RefComponentsSelector for Selector<P> {
            type Output = P;
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let mut accessor =
                    PrimitiveAccessor::<P, _>::new(components.ptr, components.offset);
                let previous_value = accessor.get();
                accessor.set(self.value);
                previous_value
            }
        }

        self.components().select(Selector { value })
    }

    #[inline]
    pub fn modify<F: FnOnce(P) -> P>(&mut self, f: F) {
        struct Selector<P, F> {
            f: F,
            phantom: PhantomData<P>,
        }
        impl<P: BitsPrimitive, F: FnOnce(P) -> P> RefComponentsSelector for Selector<P, F> {
            type Output = ();
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let mut accessor =
                    PrimitiveAccessor::<P, _>::new(components.ptr, components.offset);
                let previous_value = accessor.get();
                let new_value = (self.f)(previous_value);
                accessor.set(new_value);
            }
        }

        self.components().select(Selector::<P, F> {
            f,
            phantom: PhantomData,
        });
    }

    #[inline]
    fn components(&self) -> UntypedRefComponents {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert!(components.metadata.bit_count == P::BIT_COUNT);
        components
    }
}

pub(crate) struct PrimitiveAccessor<P: BitsPrimitive, U: BitsPrimitive> {
    ptr: NonNull<U>,
    offset: usize,
    phantom: PhantomData<P>,
}

impl<P: BitsPrimitive, U: BitsPrimitive> PrimitiveAccessor<P, U> {
    #[inline]
    pub(crate) fn new(ptr: NonNull<U>, offset: usize) -> Self {
        PrimitiveAccessor {
            ptr,
            offset,
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn get(&self) -> P {
        let mut value = P::ZERO;
        unsafe {
            copy_bits_raw(self.ptr.as_ptr(), self.offset, &mut value, 0, P::BIT_COUNT);
        }
        value
    }

    #[inline]
    fn set(&mut self, value: P) {
        unsafe {
            copy_bits_raw(&value, 0, self.ptr.as_ptr(), self.offset, P::BIT_COUNT);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Not;
    use std::ptr::NonNull;

    use crate::refrepr::TypedRefComponents;
    use crate::{BitsPrimitive, Primitive};

    #[test]
    fn read() {
        let memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory:: 10FEDCBA
        let ptr = NonNull::from(&memory[0]);
        let components = TypedRefComponents {
            ptr,
            offset: 12,
            bit_count: u8::BIT_COUNT,
        };
        let repr = components.encode();
        let p_ref: &Primitive<u8> = unsafe { std::mem::transmute(repr) };

        let value = p_ref.read();

        assert_eq!(value, 0xED);
    }

    #[test]
    fn write() {
        let mut memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory: 10FEDCBA
        let ptr = NonNull::from(&mut memory[0]);
        let components = TypedRefComponents {
            ptr,
            offset: 12,
            bit_count: u8::BIT_COUNT,
        };
        let repr = components.encode();
        let p_ref: &mut Primitive<u8> = unsafe { std::mem::transmute(repr) };

        let previous_value = p_ref.write(0x76);

        assert_eq!(previous_value, 0xED);
        assert_eq!(memory, [0x6CBA, 0x10F7]); // In memory: 10F76CBA
    }

    #[test]
    fn modify() {
        let mut memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory: 10FEDCBA
        let ptr = NonNull::from(&mut memory[0]);
        let components = TypedRefComponents {
            ptr,
            offset: 12,
            bit_count: u8::BIT_COUNT,
        };
        let repr = components.encode();
        let p_ref: &mut Primitive<u8> = unsafe { std::mem::transmute(repr) };

        p_ref.modify(Not::not);

        assert_eq!(memory, [0x2CBA, 0x10F1]); // In memory: 10F12CBA
    }
}
