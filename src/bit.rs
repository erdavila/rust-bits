use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use crate::bitvalue::BitValue;
use crate::refrepr::{
    BitPointer, RefComponentsSelector, RefRepr, TypedPointer, TypedRefComponents,
    UntypedRefComponents,
};
use crate::{BitStr, BitsPrimitive};

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
        struct Selector;
        impl RefComponentsSelector for Selector {
            type Output = BitValue;
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let accessor = BitAccessor::new(components.bit_ptr);
                accessor.get()
            }
        }

        self.components().select(Selector)
    }

    /// Sets the value of the referenced bit.
    ///
    /// It returns the previous value.
    #[inline]
    pub fn write(&mut self, value: BitValue) -> BitValue {
        struct Selector {
            value: BitValue,
        }
        impl RefComponentsSelector for Selector {
            type Output = BitValue;
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let mut accessor = BitAccessor::new(components.bit_ptr);
                let previous_value = accessor.get();
                accessor.set(self.value);
                previous_value
            }
        }

        self.components().select(Selector { value })
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
        }
        impl<F: FnOnce(BitValue) -> BitValue> RefComponentsSelector for Selector<F> {
            type Output = ();
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                let mut accessor = BitAccessor::new(components.bit_ptr);
                let previous_value = accessor.get();
                let new_value = (self.f)(previous_value);
                accessor.set(new_value);
            }
        }

        self.components().select(Selector { f });
    }

    #[inline]
    fn components(&self) -> UntypedRefComponents {
        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        let components = repr.decode();
        debug_assert_eq!(components.metadata.bit_count, 1);
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

pub(crate) struct BitAccessor<P: BitsPrimitive> {
    ptr: TypedPointer<P>,
    mask: P,
}

impl<P: BitsPrimitive> BitAccessor<P> {
    #[inline]
    pub(crate) fn new(bit_ptr: BitPointer<P>) -> Self {
        BitAccessor {
            ptr: bit_ptr.elem_ptr(),
            mask: P::ONE << bit_ptr.offset().value(),
        }
    }

    #[inline]
    pub(crate) fn get(&self) -> BitValue {
        BitValue::from((unsafe { self.ptr.read() } & self.mask) != P::ZERO)
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

impl PartialEq for Bit {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.read() == other.read()
    }
}

impl PartialEq<BitValue> for Bit {
    #[inline]
    fn eq(&self, other: &BitValue) -> bool {
        self.read() == *other
    }
}

impl PartialEq<BitValue> for &Bit {
    #[inline]
    fn eq(&self, other: &BitValue) -> bool {
        self.read() == *other
    }
}

impl PartialEq<&Bit> for BitValue {
    #[inline]
    fn eq(&self, other: &&Bit) -> bool {
        *self == other.read()
    }
}

impl PartialEq<Bit> for BitValue {
    #[inline]
    fn eq(&self, other: &Bit) -> bool {
        *self == other.read()
    }
}

impl Hash for Bit {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.read().hash(state);
    }
}

impl AsRef<BitStr> for Bit {
    #[inline]
    fn as_ref(&self) -> &BitStr {
        self.as_bit_str()
    }
}

impl AsMut<BitStr> for Bit {
    #[inline]
    fn as_mut(&mut self) -> &mut BitStr {
        self.as_bit_str_mut()
    }
}

impl Debug for Bit {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.read(), f)
    }
}

#[cfg(test)]
mod tests {
    use std::convert::identity;
    use std::hash::{Hash, Hasher};
    use std::ops::Not;

    use crate::refrepr::{BitPointer, RefRepr, TypedRefComponents};
    use crate::BitValue::{One, Zero};
    use crate::{Bit, BitStr, BitsPrimitive};

    fn new_ref<U: BitsPrimitive>(under: &U, bit_index: usize) -> &Bit {
        let repr = repr(under, bit_index);
        unsafe { std::mem::transmute(repr) }
    }

    fn new_mut<U: BitsPrimitive>(under: &U, bit_index: usize) -> &mut Bit {
        let repr = repr(under, bit_index);
        unsafe { std::mem::transmute(repr) }
    }

    fn repr<U: BitsPrimitive>(under: &U, bit_index: usize) -> RefRepr {
        let components = TypedRefComponents {
            bit_ptr: BitPointer::new_normalized(under.into(), bit_index),
            bit_count: 1,
        };
        components.encode()
    }

    #[test]
    fn read() {
        let under = 0b10010011u8;

        assert_eq!(new_ref(&under, 0).read(), One);
        assert_eq!(new_ref(&under, 1).read(), One);
        assert_eq!(new_ref(&under, 2).read(), Zero);
        assert_eq!(new_ref(&under, 3).read(), Zero);
        assert_eq!(new_ref(&under, 4).read(), One);
        assert_eq!(new_ref(&under, 5).read(), Zero);
        assert_eq!(new_ref(&under, 6).read(), Zero);
        assert_eq!(new_ref(&under, 7).read(), One);
    }

    #[test]
    fn write() {
        let under = 0b10010011u8;

        assert_eq!(new_mut(&under, 0).write(Zero), One);
        assert_eq!(new_mut(&under, 1).write(One), One);
        assert_eq!(new_mut(&under, 2).write(Zero), Zero);
        assert_eq!(new_mut(&under, 3).write(One), Zero);
        assert_eq!(under, 0b10011010);
    }

    #[test]
    fn modify() {
        let under = 0b10010011u8;

        new_mut(&under, 4).modify(Not::not);
        new_mut(&under, 5).modify(Not::not);
        new_mut(&under, 6).modify(identity);
        new_mut(&under, 7).modify(identity);

        assert_eq!(under, 0b10100011);
    }

    #[test]
    fn eq() {
        let x = 0b1010u8;
        let bit0 = new_ref(&x, 0);
        let bit1 = new_ref(&x, 1);
        let bit2 = new_ref(&x, 2);
        let bit3 = new_ref(&x, 3);

        assert!(bit0 == bit0);
        assert!(bit0 == bit2);
        assert!(bit0 == Zero);
        assert!(bit0 == &Zero);
        assert!(Zero == bit0);
        assert!(&Zero == bit0);

        assert!(bit0 != bit1);

        assert!(bit1 == bit1);
        assert!(bit1 == bit3);
        assert!(bit1 == One);
        assert!(bit1 == &One);
        assert!(One == bit1);
        assert!(&One == bit1);
    }

    #[test]
    fn hash() {
        fn hash_value<H: Hash>(h: H) -> u64 {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            h.hash(&mut s);
            s.finish()
        }

        let x = 0b10u8;
        let bit0 = new_ref(&x, 0);
        let bit1 = new_ref(&x, 1);

        assert_eq!(hash_value(bit0), hash_value(Zero));
        assert_eq!(hash_value(bit1), hash_value(One));
    }

    #[test]
    fn as_ref() {
        let memory = [0b10010011u8];
        let bit_str = BitStr::new_ref(&memory);
        for (i, value) in [One, One, Zero, Zero, One, Zero, Zero, One]
            .into_iter()
            .enumerate()
        {
            let bit_ref = bit_str.get_ref(i).unwrap();

            let bit_str: &BitStr = bit_ref.as_ref();

            assert_eq!(bit_str, &[value]);
        }
    }

    #[test]
    fn as_mut() {
        let mut memory = [0b10010011u8];
        let bit_str = BitStr::new_mut(&mut memory);
        for bit_ref in bit_str.iter_mut() {
            //

            let bit_str: &mut BitStr = bit_ref.as_mut();

            bit_str.get_mut(0).unwrap().modify(Not::not);
        }
        assert_eq!(memory, [0b01101100]);
    }
}
