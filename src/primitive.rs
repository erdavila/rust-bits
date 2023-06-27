use std::hash::Hash;
use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::copy_bits::copy_bits_raw;
use crate::refrepr::{RefComponentsSelector, RefRepr, TypedRefComponents, UntypedRefComponents};
use crate::BitsPrimitive;

#[repr(C)]
#[derive(Eq)]
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

impl<P: BitsPrimitive> PartialEq for Primitive<P> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        *self == other.read()
    }
}

impl<P: BitsPrimitive> PartialEq<P> for Primitive<P> {
    #[inline]
    fn eq(&self, other: &P) -> bool {
        self.read() == *other
    }
}

impl<P: BitsPrimitive> Hash for Primitive<P> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.read().hash(state);
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Not;
    use std::ptr::NonNull;

    use crate::refrepr::{RefRepr, TypedRefComponents};
    use crate::{BitsPrimitive, Primitive};

    fn new_ref<P: BitsPrimitive, U: BitsPrimitive>(under: &U, offset: usize) -> &Primitive<P> {
        let repr = repr::<P, U>(under, offset);
        unsafe { std::mem::transmute(repr) }
    }

    fn new_mut<P: BitsPrimitive, U: BitsPrimitive>(
        under: &mut U,
        offset: usize,
    ) -> &mut Primitive<P> {
        let repr = repr::<P, U>(under, offset);
        unsafe { std::mem::transmute(repr) }
    }

    fn repr<P: BitsPrimitive, U: BitsPrimitive>(under: &U, offset: usize) -> RefRepr {
        let components =
            TypedRefComponents::new_normalized(NonNull::from(under), offset, P::BIT_COUNT);
        components.encode()
    }

    #[test]
    fn read() {
        let memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory:: 10FEDCBA
        let p_ref: &Primitive<u8> = new_ref(&memory[0], 12);

        let value = p_ref.read();

        assert_eq!(value, 0xED);
    }

    #[test]
    fn write() {
        let mut memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory:: 10FEDCBA
        let p_ref: &mut Primitive<u8> = new_mut(&mut memory[0], 12);

        let previous_value = p_ref.write(0x76);

        assert_eq!(previous_value, 0xED);
        assert_eq!(memory, [0x6CBA, 0x10F7]); // In memory: 10F76CBA
    }

    #[test]
    fn modify() {
        let mut memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory:: 10FEDCBA
        let p_ref: &mut Primitive<u8> = new_mut(&mut memory[0], 12);

        p_ref.modify(Not::not);

        assert_eq!(memory, [0x2CBA, 0x10F1]); // In memory: 10F12CBA
    }

    #[test]
    fn eq() {
        let memory: [u16; 2] = [0xDCBA, 0xEDCE]; // In memory: EDCEDCBA
        let p1: &Primitive<u8> = new_ref(&memory[0], 12);
        let p2: &Primitive<u8> = new_ref(&memory[0], 24);
        let p_ne: &Primitive<u8> = new_ref(&memory[0], 0);

        assert!(p1 == p1);
        assert!(p1 == p2);
        assert!(p1 == &0xED);

        assert!(p1 != p_ne);
    }
}
