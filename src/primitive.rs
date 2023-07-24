use std::hash::Hash;
use std::marker::PhantomData;

use crate::copy_bits::copy_bits_ptr;
use crate::refrepr::{
    BitPointer, RefComponentsSelector, RefRepr, TypedRefComponents, UntypedRefComponents,
};
use crate::{BitStr, BitsPrimitive};

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
                let accessor = PrimitiveAccessor::<P, _>::new(components.bit_ptr);
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
                let mut accessor = PrimitiveAccessor::<P, _>::new(components.bit_ptr);
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
                let mut accessor = PrimitiveAccessor::<P, _>::new(components.bit_ptr);
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

    #[inline]
    pub fn as_bit_str(&self) -> &BitStr {
        unsafe { std::mem::transmute(self) }
    }

    #[inline]
    pub fn as_bit_str_mut(&mut self) -> &mut BitStr {
        unsafe { std::mem::transmute(self) }
    }
}

pub(crate) struct PrimitiveAccessor<P: BitsPrimitive, U: BitsPrimitive> {
    bit_ptr: BitPointer<U>,
    phantom: PhantomData<P>,
}

impl<P: BitsPrimitive, U: BitsPrimitive> PrimitiveAccessor<P, U> {
    #[inline]
    pub(crate) fn new(bit_ptr: BitPointer<U>) -> Self {
        PrimitiveAccessor {
            bit_ptr,
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn get(&self) -> P {
        let mut value = P::ZERO;

        let src = self.bit_ptr;
        let dst = BitPointer::new_normalized((&mut value).into(), 0);
        unsafe {
            copy_bits_ptr(src, dst, P::BIT_COUNT);
        }

        value
    }

    #[inline]
    fn set(&mut self, value: P) {
        let src = BitPointer::new_normalized((&value).into(), 0);
        let dst = self.bit_ptr;

        unsafe {
            copy_bits_ptr(src, dst, P::BIT_COUNT);
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
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.read().hash(state);
    }
}

impl<P: BitsPrimitive> AsRef<BitStr> for Primitive<P> {
    #[inline]
    fn as_ref(&self) -> &BitStr {
        self.as_bit_str()
    }
}

impl<P: BitsPrimitive> AsMut<BitStr> for Primitive<P> {
    #[inline]
    fn as_mut(&mut self) -> &mut BitStr {
        self.as_bit_str_mut()
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Not;

    use crate::refrepr::{BitPointer, RefRepr, TypedRefComponents};
    use crate::{BitStr, BitsPrimitive, Primitive};

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
        let components = TypedRefComponents {
            bit_ptr: BitPointer::new_normalized(under.into(), offset),
            bit_count: P::BIT_COUNT,
        };
        components.encode()
    }

    #[test]
    fn read() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x10]; // In memory:: 10FEDCBA
        let p_ref: &Primitive<u8> = new_ref(&memory[0], 12);

        let value = p_ref.read();

        assert_eq!(value, 0xED);
    }

    #[test]
    fn write() {
        let mut memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x10]; // In memory:: 10FEDCBA
        let p_ref: &mut Primitive<u8> = new_mut(&mut memory[0], 12);

        let previous_value = p_ref.write(0x76);

        assert_eq!(previous_value, 0xED);
        assert_eq!(memory, [0xBA, 0x6C, 0xF7, 0x10]); // In memory: 10F76CBA
    }

    #[test]
    fn modify() {
        let mut memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x10]; // In memory:: 10FEDCBA
        let p_ref: &mut Primitive<u8> = new_mut(&mut memory[0], 12);

        p_ref.modify(Not::not);

        assert_eq!(memory, [0xBA, 0x2C, 0xF1, 0x10]); // In memory: 10F12CBA
    }

    #[test]
    fn eq() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xCE, 0xED]; // In memory: EDCEDCBA
        let p1: &Primitive<u8> = new_ref(&memory[0], 12);
        let p2: &Primitive<u8> = new_ref(&memory[0], 24);
        let p_ne: &Primitive<u8> = new_ref(&memory[0], 0);

        assert!(p1 == p1);
        assert!(p1 == p2);
        assert!(p1 == &0xED);

        assert!(p1 != p_ne);
    }

    #[test]
    fn as_ref() {
        let memory: [u8; 2] = [0xBA, 0xDC];
        let p_ref: &Primitive<u8> = BitStr::new_ref(&memory)[1..15]
            .get_primitive_ref(3)
            .unwrap();

        let bit_ref: &BitStr = p_ref.as_ref();

        assert_eq!(bit_ref, &BitStr::new_ref(&memory)[4..12]);
    }

    #[test]
    fn as_mut() {
        let mut memory: [u8; 2] = [0xBA, 0xDC];
        let p_ref: &mut Primitive<u8> = BitStr::new_mut(&mut memory)[1..15]
            .get_primitive_mut(3)
            .unwrap();

        let bit_ref: &mut BitStr = p_ref.as_mut();

        for bit in bit_ref.iter_mut() {
            bit.modify(Not::not);
        }
        assert_eq!(memory, [0x4A, 0xD3]);
    }
}
