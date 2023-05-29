use crate::bitvalue::BitValue;
use crate::primitivetype::{PrimitiveType, DISCRIMINANT_BIT_COUNT, DISCRIMINANT_MASK};

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
    pub fn new_ref<P: PrimitiveType>(p: &P, bit_index: usize) -> &Self {
        let parts = DstRefParts::new(p, bit_index);
        unsafe { std::mem::transmute(parts) }
    }

    /// Creates a reference to a single mutable bit.
    ///
    /// # Panics
    ///
    /// It panics if the `bit_index` is too high for the primitive type.
    pub fn new_mut<P: PrimitiveType>(p: &mut P, bit_index: usize) -> &mut Self {
        let parts = DstRefParts::new(p, bit_index);
        unsafe { std::mem::transmute(parts) }
    }

    /// Gets the value of the referenced bit.
    pub fn get(&self) -> BitValue {
        fn get<P: PrimitiveType>(parts: DstRefParts) -> BitValue {
            let p = unsafe { raw_ptr_to_ref(parts.ptr) };
            let mask = Mask::<P>::new(parts.bit_index());
            mask.get_bit_value(p)
        }

        let parts: DstRefParts = unsafe { std::mem::transmute(self) };

        match parts.discriminant() {
            usize::DISCRIMINANT => get::<usize>(parts),
            u8::DISCRIMINANT => get::<u8>(parts),
            u16::DISCRIMINANT => get::<u16>(parts),
            u32::DISCRIMINANT => get::<u32>(parts),
            u64::DISCRIMINANT => get::<u64>(parts),
            u128::DISCRIMINANT => get::<u128>(parts),
            _ => unreachable!(),
        }
    }

    /// Sets the value of the referenced bit.
    ///
    /// It returns the previous value.
    pub fn set(&mut self, value: BitValue) -> BitValue {
        fn set<P: PrimitiveType>(value: BitValue, parts: DstRefParts) -> BitValue {
            let p = unsafe { raw_ptr_to_mut::<P>(parts.ptr) };
            let mask = Mask::<P>::new(parts.bit_index());
            let previous_value = mask.get_bit_value(p);
            mask.set_bit_value(p, value);
            previous_value
        }

        let parts: DstRefParts = unsafe { std::mem::transmute(self) };

        match parts.discriminant() {
            usize::DISCRIMINANT => set::<usize>(value, parts),
            u8::DISCRIMINANT => set::<u8>(value, parts),
            u16::DISCRIMINANT => set::<u16>(value, parts),
            u32::DISCRIMINANT => set::<u32>(value, parts),
            u64::DISCRIMINANT => set::<u64>(value, parts),
            u128::DISCRIMINANT => set::<u128>(value, parts),
            _ => unreachable!(),
        }
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
        fn modify<P: PrimitiveType>(f: impl FnOnce(BitValue) -> BitValue, parts: DstRefParts) {
            let p = unsafe { raw_ptr_to_mut::<P>(parts.ptr) };
            let mask = Mask::<P>::new(parts.bit_index());
            let previous_value = mask.get_bit_value(p);
            let new_value = f(previous_value);
            mask.set_bit_value(p, new_value);
        }

        let parts: DstRefParts = unsafe { std::mem::transmute(self) };

        match parts.discriminant() {
            usize::DISCRIMINANT => modify::<usize>(f, parts),
            u8::DISCRIMINANT => modify::<u8>(f, parts),
            u16::DISCRIMINANT => modify::<u16>(f, parts),
            u32::DISCRIMINANT => modify::<u32>(f, parts),
            u64::DISCRIMINANT => modify::<u64>(f, parts),
            u128::DISCRIMINANT => modify::<u128>(f, parts),
            _ => unreachable!(),
        }
    }
}

unsafe fn raw_ptr_to_ref<'a, P: PrimitiveType>(ptr: *const ()) -> &'a P {
    &*(ptr as *const P)
}

unsafe fn raw_ptr_to_mut<'a, P: PrimitiveType>(ptr: *const ()) -> &'a mut P {
    &mut *(ptr as *mut P)
}

#[repr(C)]
struct DstRefParts {
    ptr: *const (),
    metadata: usize,
}

impl DstRefParts {
    fn new<P: PrimitiveType>(ptr: *const P, bit_index: usize) -> Self {
        assert!(bit_index < P::BIT_COUNT, "invalid bit index");
        DstRefParts {
            ptr: ptr as _,
            metadata: (bit_index << DISCRIMINANT_BIT_COUNT) | (P::DISCRIMINANT & DISCRIMINANT_MASK),
        }
    }

    fn discriminant(&self) -> usize {
        self.metadata & DISCRIMINANT_MASK
    }

    fn bit_index(&self) -> usize {
        self.metadata >> DISCRIMINANT_BIT_COUNT
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

#[cfg(test)]
mod tests {
    use std::ops::Not;

    use crate::Bit;
    use crate::BitValue::{One, Zero};

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
    #[should_panic(expected = "invalid bit index")]
    fn new_ref_invalid_bit_index() {
        let p = 0b_11110000_10010011_u16;

        Bit::new_ref(&p, 16);
    }

    #[test]
    #[should_panic(expected = "invalid bit index")]
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
}
