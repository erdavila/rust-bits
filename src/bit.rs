use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use crate::bitvalue::BitValue;
use crate::primitivetype::PrimitiveType;
use crate::refs::{
    DstMutRefRepr, DstMutRefReprExecutor, DstRefRepr, DstRefReprExecutor, MutRefComponents,
    RefComponents,
};
use crate::{BitStr, UnderlyingPrimitives};

/// Representation of a reference to a single bit in a [primitive].
///
/// The bit cannot be directly dereferenced. Instead, it must be read with the
/// [`get`] method and changed with the [`set`] and [`modify`] methods.
///
/// # Example
///
/// ```
/// use rust_bits::{Bit, BitValue};
///
/// let mut n: u8 = 0b_1100_1001;
///
/// let bit_ref: &Bit = Bit::new_ref(&n, 4);
/// assert_eq!(bit_ref.get(), BitValue::Zero);
///
/// let bit_ref: &mut Bit = Bit::new_mut(&mut n, 4);
/// let previous_value = bit_ref.set(BitValue::One);
/// assert_eq!(previous_value, BitValue::Zero);
/// assert_eq!(n, 0b_1101_1001);
/// ```
///
/// [primitive]: PrimitiveType
/// [`get`]: Bit::get
/// [`set`]: Bit::set
/// [`modify`]: Bit::modify
#[repr(C)]
#[derive(Eq)]
pub struct Bit {
    _unsized: [()],
}

impl Bit {
    /// Creates a reference to a single bit.
    ///
    /// # Panics
    ///
    /// It panics if the `bit_index` is too high for the primitive type.
    pub fn new_ref<U: UnderlyingPrimitives>(under: &U, bit_index: usize) -> &Self {
        let repr = DstRefRepr::encode(under, bit_index, 1);
        unsafe { std::mem::transmute(repr) }
    }

    /// Creates a reference to a single mutable bit.
    ///
    /// # Panics
    ///
    /// It panics if the `bit_index` is too high for the primitive type.
    pub fn new_mut<U: UnderlyingPrimitives>(under: &mut U, bit_index: usize) -> &mut Self {
        let repr = DstMutRefRepr::encode(under, bit_index, 1);
        unsafe { std::mem::transmute(repr) }
    }

    /// Gets the value of the referenced bit.
    pub fn get(&self) -> BitValue {
        struct Executor;

        impl DstRefReprExecutor<'_> for Executor {
            type Output = BitValue;

            fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output {
                let under = components.get_ref();
                let mask = Mask::<U>::new(components.offset);
                mask.get_bit_value(under)
            }
        }

        self.repr().decode_and_execute(Executor)
    }

    /// Sets the value of the referenced bit.
    ///
    /// It returns the previous value.
    pub fn set(&mut self, value: BitValue) -> BitValue {
        struct Executor {
            value: BitValue,
        }

        impl<'a> DstMutRefReprExecutor<'a> for Executor {
            type Output = BitValue;

            fn execute<P: PrimitiveType + 'a>(
                self,
                mut components: MutRefComponents<'a, P>,
            ) -> Self::Output {
                let mask = Mask::<P>::new(components.offset);
                let under = components.get_ref();
                let previous_value = mask.get_bit_value(under);
                mask.set_bit_value(under, self.value);
                previous_value
            }
        }

        self.repr_mut().decode_and_execute(Executor { value })
    }

    /// Allows retrieving and setting the bit value in a single operation.
    ///
    /// The passed closure receives the current value and must return the new value.
    ///
    /// # Example
    ///
    /// ```
    /// use rust_bits::{Bit, BitValue::One};
    ///
    /// let mut byte: u8 = 0b_0010_0000;
    ///
    /// // Flips the bits by XORing with `One`
    /// Bit::new_mut(&mut byte, 4).modify(|b| b ^ One);
    /// Bit::new_mut(&mut byte, 5).modify(|b| b ^ One);
    ///
    /// assert_eq!(byte, 0b_0001_0000);
    /// ```
    pub fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(BitValue) -> BitValue,
    {
        struct Executor<F: FnOnce(BitValue) -> BitValue> {
            f: F,
        }

        impl<'a, F: FnOnce(BitValue) -> BitValue> DstMutRefReprExecutor<'a> for Executor<F> {
            type Output = ();
            fn execute<U: PrimitiveType + 'a>(
                self,
                mut components: MutRefComponents<'a, U>,
            ) -> Self::Output {
                let mask = Mask::<U>::new(components.offset);
                let under = components.get_ref();
                let previous_value = mask.get_bit_value(under);
                let new_value = (self.f)(previous_value);
                mask.set_bit_value(under, new_value);
            }
        }

        self.repr_mut().decode_and_execute(Executor { f });
    }

    pub fn as_bit_str(&self) -> &BitStr {
        unsafe { std::mem::transmute(self) }
    }

    pub fn as_bit_str_mut(&mut self) -> &mut BitStr {
        unsafe { std::mem::transmute(self) }
    }

    fn repr(&self) -> DstRefRepr {
        unsafe { std::mem::transmute(self) }
    }

    fn repr_mut(&mut self) -> DstMutRefRepr {
        unsafe { std::mem::transmute(self) }
    }
}

struct Mask<P: PrimitiveType>(P);

impl<P: PrimitiveType> Mask<P> {
    fn new(bit_index: usize) -> Self {
        Self(P::ONE << bit_index)
    }

    fn get_bit_value(&self, p: &P) -> BitValue {
        BitValue::from((*p & self.0) != P::ZERO)
    }

    fn set_bit_value(&self, p: &mut P, value: BitValue) {
        match value {
            BitValue::Zero => *p &= !self.0,
            BitValue::One => *p |= self.0,
        }
    }
}

impl PartialEq for Bit {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl PartialEq<BitValue> for Bit {
    fn eq(&self, other: &BitValue) -> bool {
        self.get() == *other
    }
}

impl PartialEq<BitValue> for &Bit {
    fn eq(&self, other: &BitValue) -> bool {
        self.get() == *other
    }
}

impl PartialEq<&Bit> for BitValue {
    fn eq(&self, other: &&Bit) -> bool {
        *self == other.get()
    }
}

impl PartialEq<Bit> for BitValue {
    fn eq(&self, other: &Bit) -> bool {
        *self == other.get()
    }
}

impl Hash for Bit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

impl Debug for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.get(), f)
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};
    use std::ops::Not;

    use crate::BitValue::{One, Zero};
    use crate::{Bit, BitStr};

    #[test]
    fn immutable() {
        let p = 0b_11110000_10010011_u16;

        let bit_ref: &Bit = Bit::new_ref(&p, 0);
        assert_eq!(bit_ref.get(), One);

        assert_eq!(Bit::new_ref(&p, 0).get(), One);
        assert_eq!(Bit::new_ref(&p, 1).get(), One);
        assert_eq!(Bit::new_ref(&p, 2).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 3).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 4).get(), One);
        assert_eq!(Bit::new_ref(&p, 5).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 6).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 7).get(), One);

        assert_eq!(Bit::new_ref(&p, 8).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 9).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 10).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 11).get(), Zero);
        assert_eq!(Bit::new_ref(&p, 12).get(), One);
        assert_eq!(Bit::new_ref(&p, 13).get(), One);
        assert_eq!(Bit::new_ref(&p, 14).get(), One);
        assert_eq!(Bit::new_ref(&p, 15).get(), One);
    }

    #[test]
    fn mutable() {
        let mut p = 0b_11110000_10010011_u16;

        assert_eq!(Bit::new_mut(&mut p, 0).set(Zero), One); // 1 -> 0
        assert_eq!(Bit::new_mut(&mut p, 1).set(One), One); // 1 -> 1
        assert_eq!(Bit::new_mut(&mut p, 2).set(One), Zero); // 0 -> 1
        assert_eq!(Bit::new_mut(&mut p, 3).set(Zero), Zero); // 0 -> 0
        Bit::new_mut(&mut p, 4).modify(Not::not); // 1 -> 0
        Bit::new_mut(&mut p, 5).modify(Not::not); // 0 -> 1

        assert_eq!(p, 0b_11110000_10100110_u16);
    }

    #[test]
    #[should_panic(expected = "invalid bit offset")]
    fn new_ref_invalid_bit_index() {
        let p = 0b_11110000_10010011_u16;

        Bit::new_ref(&p, 16);
    }

    #[test]
    #[should_panic(expected = "invalid bit offset")]
    fn new_mut_invalid_bit_index() {
        let mut p = 0b_11110000_10010011_u16;

        Bit::new_mut(&mut p, 16);
    }

    #[test]
    fn eq() {
        let x = 0b1010u8;
        let bit0 = Bit::new_ref(&x, 0);
        let bit1 = Bit::new_ref(&x, 1);
        let bit2 = Bit::new_ref(&x, 2);
        let bit3 = Bit::new_ref(&x, 3);

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
        let bit0 = Bit::new_ref(&x, 0);
        let bit1 = Bit::new_ref(&x, 1);

        assert_eq!(hash_value(bit0), hash_value(Zero));
        assert_eq!(hash_value(bit1), hash_value(One));
    }

    #[test]
    fn as_bit_str() {
        let under = 0u8;
        let bit = Bit::new_ref(&under, 0);

        let bit_str: &BitStr = bit.as_bit_str();

        assert_eq!(bit_str.len(), 1);
    }
}
