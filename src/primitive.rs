use std::hash::Hash;
use std::marker::PhantomData;
use std::slice;

use crate::copy_bits::copy_bits_ptr;
use crate::copy_bits::copy_bits_to_primitives;
use crate::copy_bits::copy_primitives_to_bits;
use crate::ref_encoding::bit_pointer::BitPointer;
use crate::ref_encoding::{RefComponents, RefRepr};
use crate::refrepr::BitPointer as LegacyBitPointer;
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
        self.accessor().get()
    }

    #[inline]
    pub fn write(&mut self, value: P) -> P {
        let mut accessor = self.accessor();
        let previous_value = accessor.get();
        accessor.set(value);
        previous_value
    }

    #[inline]
    pub fn modify<F: FnOnce(P) -> P>(&mut self, f: F) {
        let mut accessor = self.accessor();
        let previous_value = accessor.get();
        let new_value = f(previous_value);
        accessor.set(new_value);
    }

    #[inline]
    fn accessor(&self) -> PrimitiveAccessor<P> {
        let components = self.ref_components();
        PrimitiveAccessor::new(components.bit_ptr)
    }

    #[inline]
    fn ref_components(&self) -> RefComponents {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert!(components.bit_count == P::BIT_COUNT);
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

pub(crate) struct PrimitiveAccessor<P: BitsPrimitive> {
    bit_ptr: BitPointer,
    phantom: PhantomData<P>,
}

impl<P: BitsPrimitive> PrimitiveAccessor<P> {
    #[inline]
    pub(crate) fn new(bit_ptr: BitPointer) -> Self {
        PrimitiveAccessor {
            bit_ptr,
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn get(&self) -> P {
        self.get_lower_bits(P::BIT_COUNT)
    }

    #[inline]
    pub(crate) fn get_lower_bits(&self, count: usize) -> P {
        let mut primitive = P::ZERO;
        unsafe { copy_bits_to_primitives(self.bit_ptr, slice::from_mut(&mut primitive), count) };
        primitive
    }

    #[inline]
    fn set(&mut self, value: P) {
        unsafe { copy_primitives_to_bits(slice::from_ref(&value), self.bit_ptr, P::BIT_COUNT) };
    }
}

pub(crate) struct LegacyPrimitiveAccessor<P: BitsPrimitive, U: BitsPrimitive> {
    bit_ptr: LegacyBitPointer<U>,
    phantom: PhantomData<P>,
}

impl<P: BitsPrimitive, U: BitsPrimitive> LegacyPrimitiveAccessor<P, U> {
    #[inline]
    pub(crate) fn new(bit_ptr: LegacyBitPointer<U>) -> Self {
        LegacyPrimitiveAccessor {
            bit_ptr,
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn get(&self) -> P {
        let mut value = P::ZERO;

        let src = self.bit_ptr;
        let dst = LegacyBitPointer::new_normalized((&mut value).into(), 0);
        unsafe {
            copy_bits_ptr(src, dst, P::BIT_COUNT);
        }

        value
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

    use crate::ref_encoding::bit_pointer::BitPointer;
    use crate::ref_encoding::{RefComponents, RefRepr};
    use crate::{BitStr, BitsPrimitive, Primitive};

    fn new_ref<P: BitsPrimitive>(under: &u8, offset: usize) -> &Primitive<P> {
        let repr = repr::<P>(under, offset);
        unsafe { std::mem::transmute(repr) }
    }

    fn new_mut<P: BitsPrimitive>(under: &mut u8, offset: usize) -> &mut Primitive<P> {
        let repr = repr::<P>(under, offset);
        unsafe { std::mem::transmute(repr) }
    }

    fn repr<P: BitsPrimitive>(under: &u8, offset: usize) -> RefRepr {
        let components = RefComponents {
            bit_ptr: BitPointer::new_normalized(under.into(), offset),
            bit_count: P::BIT_COUNT,
        };
        components.encode()
    }

    #[test]
    fn read() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x10]; // In memory:: 10FEDCBA

        {
            let p_ref: &Primitive<u16> = new_ref(&memory[0], 8);

            let value = p_ref.read();

            assert_eq!(value, 0xFEDC);
        }

        {
            let p_ref: &Primitive<u16> = new_ref(&memory[0], 4);

            let value = p_ref.read();

            assert_eq!(value, 0xEDCB);
        }
    }

    #[test]
    fn write() {
        let mut memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x10]; // In memory:: 10FEDCBA

        {
            let p_ref: &mut Primitive<u16> = new_mut(&mut memory[0], 8);

            let previous_value = p_ref.write(0x9876);

            assert_eq!(previous_value, 0xFEDC);
            assert_eq!(memory, [0xBA, 0x76, 0x98, 0x10]); // In memory: 109876BA
        }

        {
            let p_ref: &mut Primitive<u16> = new_mut(&mut memory[0], 4);

            let previous_value = p_ref.write(0x5432);

            assert_eq!(previous_value, 0x876B);
            assert_eq!(memory, [0x2A, 0x43, 0x95, 0x10]); // In memory: 1095432A
        }
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
