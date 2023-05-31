use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use crate::refs::DstRefRepr;
use crate::PrimitiveType;

/// Representation of a reference to a [primitive] composed by contiguous bits
/// anywhere in underlying primitives.
///
/// The referenced [primitive] cannot be directly dereferenced. Instead, it must
/// be accessed using the methods in this struct.
///
/// The referenced primitive can have any bit-alignment, an can span multiple
/// underlying primitives.
///
/// ```
/// use rust_bits::Primitive;
///
/// let mut underlying: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: 0xFEDCBA
///
/// let u16_ref: &Primitive<u16> = Primitive::new_ref(&underlying, 4);
/// assert_eq!(u16_ref.get(), 0xEDCBu16);
///
/// let u16_ref: &mut Primitive<u16> = Primitive::new_mut(&mut underlying, 4);
/// u16_ref.set(0x1234);
/// assert_eq!(underlying, [0x4A, 0x23, 0xF1]);
/// ```
///
/// [primitive]: PrimitiveType
#[repr(C)]
#[derive(Eq)]
pub struct Primitive<P: PrimitiveType> {
    _phantom: PhantomData<P>,
    _unsized: [()],
}

impl<P: PrimitiveType> Primitive<P> {
    /// Creates a reference to a primitive.
    ///
    /// # Panics
    ///
    /// It panics if the bits of the referenced primitive don't fit entirely in
    /// the underlying primitives.
    ///
    /// ```should_panic
    /// use rust_bits::Primitive;
    ///
    /// let underlying: [u8; 2] = [0xBA, 0xDC]; // In memory: 0xDCBA
    /// let _: &Primitive<u16> = Primitive::new_ref(&underlying, 4);
    /// ```
    pub fn new_ref<U: PrimitiveType>(under: &[U], first_bit_index: usize) -> &Self {
        let parts = DstRefRepr::new(under, first_bit_index, P::BIT_COUNT);
        unsafe { std::mem::transmute(parts) }
    }

    /// Creates a reference to a mutable primitive.
    ///
    /// # Panics
    ///
    /// It panics if the bits of the referenced primitive don't fit entirely in
    /// the underlying primitives.
    ///
    /// ```should_panic
    /// use rust_bits::Primitive;
    ///
    /// let mut underlying: [u8; 2] = [0xBA, 0xDC]; // In memory: 0xDCBA
    /// let _: &mut Primitive<u16> = Primitive::new_mut(&mut underlying, 4);
    /// ```
    pub fn new_mut<U: PrimitiveType>(under: &mut [U], first_bit_index: usize) -> &mut Self {
        let parts = DstRefRepr::new(under, first_bit_index, P::BIT_COUNT);
        unsafe { std::mem::transmute(parts) }
    }

    /// Gets the value of the referenced primitive.
    pub fn get(&self) -> P {
        fn get<P: PrimitiveType, U: PrimitiveType>(parts: DstRefRepr) -> P {
            let ptr = parts.ptr();
            let access = PrimitiveAccess::<P, U>::new(parts.offset());
            access.get_primitive(ptr)
        }

        let parts: DstRefRepr = unsafe { std::mem::transmute(self) };

        match parts.discriminant() {
            usize::DISCRIMINANT => get::<P, usize>(parts),
            u8::DISCRIMINANT => get::<P, u8>(parts),
            u16::DISCRIMINANT => get::<P, u16>(parts),
            u32::DISCRIMINANT => get::<P, u32>(parts),
            u64::DISCRIMINANT => get::<P, u64>(parts),
            u128::DISCRIMINANT => get::<P, u128>(parts),
            _ => unreachable!(),
        }
    }

    /// Sets the value of the referenced primitive.
    ///
    /// It returns the previous value.
    pub fn set(&mut self, value: P) -> P {
        fn set<P: PrimitiveType, U: PrimitiveType>(value: P, parts: DstRefRepr) -> P {
            let ptr = parts.mut_ptr();
            let access = PrimitiveAccess::<P, U>::new(parts.offset());
            let previous_value = access.get_primitive(ptr);
            access.set_primitive(ptr, value);
            previous_value
        }

        let parts: DstRefRepr = unsafe { std::mem::transmute(self) };

        match parts.discriminant() {
            usize::DISCRIMINANT => set::<P, usize>(value, parts),
            u8::DISCRIMINANT => set::<P, u8>(value, parts),
            u16::DISCRIMINANT => set::<P, u16>(value, parts),
            u32::DISCRIMINANT => set::<P, u32>(value, parts),
            u64::DISCRIMINANT => set::<P, u64>(value, parts),
            u128::DISCRIMINANT => set::<P, u128>(value, parts),
            _ => unreachable!(),
        }
    }

    /// Allows retrieving and setting the referenced primitive value in a single
    /// operation.
    ///
    /// The passed closure receives the current value and must return the new value.
    ///
    /// # Example
    ///
    /// ```
    /// use rust_bits::Primitive;
    /// use std::ops::Not;
    ///
    /// let mut underlying: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: 0xFEDCBA
    ///
    /// let u16_ref: &mut Primitive<u16> = Primitive::new_mut(&mut underlying, 4);
    /// u16_ref.modify(Not::not);
    /// assert_eq!(underlying, [0x4A, 0x23, 0xF1]); // In memory: 0xF1234A
    /// ```
    pub fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(P) -> P,
    {
        fn modify<P: PrimitiveType, U: PrimitiveType>(f: impl FnOnce(P) -> P, parts: DstRefRepr) {
            let ptr = parts.mut_ptr();
            let access = PrimitiveAccess::<P, U>::new(parts.offset());
            let previous_value = access.get_primitive(ptr);
            let new_value = f(previous_value);
            access.set_primitive(ptr, new_value);
        }

        let parts: DstRefRepr = unsafe { std::mem::transmute(self) };

        match parts.discriminant() {
            usize::DISCRIMINANT => modify::<P, usize>(f, parts),
            u8::DISCRIMINANT => modify::<P, u8>(f, parts),
            u16::DISCRIMINANT => modify::<P, u16>(f, parts),
            u32::DISCRIMINANT => modify::<P, u32>(f, parts),
            u64::DISCRIMINANT => modify::<P, u64>(f, parts),
            u128::DISCRIMINANT => modify::<P, u128>(f, parts),
            _ => unreachable!(),
        }
    }
}

impl<P: PrimitiveType> PartialEq for Primitive<P> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<P: PrimitiveType> PartialEq<P> for Primitive<P> {
    fn eq(&self, other: &P) -> bool {
        self.get() == *other
    }
}

impl<P: PrimitiveType> Hash for Primitive<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

struct PrimitiveAccess<P: PrimitiveType, U: PrimitiveType> {
    offset: usize,
    phantom: PhantomData<(P, U)>,
}

impl<P: PrimitiveType, U: PrimitiveType> PrimitiveAccess<P, U> {
    fn new(offset: usize) -> Self {
        PrimitiveAccess {
            offset,
            phantom: PhantomData,
        }
    }

    fn get_primitive(&self, mut ptr: *const U) -> P {
        let mut available = CountedBits::new(unsafe { *ptr });
        available.drop(self.offset);

        let mut resolved = CountedBits::with_count(P::ZERO, 0);

        while resolved.count < P::BIT_COUNT {
            if available.count == 0 {
                ptr = unsafe { ptr.add(1) };
                available = CountedBits::new(unsafe { *ptr });
            }

            let transfered = available.pop_lsb::<P>();
            resolved.push_msb(transfered);
        }

        resolved.bits
    }

    fn set_primitive(&self, mut ptr: *mut U, value: P) {
        let mut available = CountedBits::new(value);
        let mut destination = MaskedBits::with_offset(unsafe { &mut *ptr }, self.offset);

        while available.count > 0 {
            if destination.is_full() {
                ptr = unsafe { ptr.add(1) };
                destination = MaskedBits::new(unsafe { &mut *ptr });
            }

            let transfered = available.pop_lsb_at_most::<U>(destination.room());
            destination.set_next(transfered);
        }
    }
}

struct CountedBits<P: PrimitiveType> {
    bits: P,
    count: usize,
}

impl<P: PrimitiveType> CountedBits<P> {
    fn new(bits: P) -> Self {
        Self::with_count(bits, P::BIT_COUNT)
    }

    fn with_count(bits: P, count: usize) -> Self {
        CountedBits { bits, count }
    }

    fn drop(&mut self, bit_count: usize) {
        if bit_count >= self.count {
            self.bits = P::ZERO;
            self.count = 0;
        } else {
            self.bits >>= bit_count;
            self.count -= bit_count;
        }
    }

    fn pop_lsb<T: PrimitiveType>(&mut self) -> CountedBits<T> {
        self.pop_lsb_at_most(T::BIT_COUNT)
    }

    fn pop_lsb_at_most<T: PrimitiveType>(&mut self, at_most: usize) -> CountedBits<T> {
        let value = T::from_usize(self.bits.to_usize());
        let count = [self.count, at_most, <usize as PrimitiveType>::BIT_COUNT]
            .into_iter()
            .min()
            .unwrap_or_default();
        self.drop(count);
        CountedBits::with_count(value, count)
    }

    fn push_msb(&mut self, msb: CountedBits<P>) {
        self.bits |= msb.bits << self.count;
        self.count += msb.count;
    }
}

impl<P: PrimitiveType> Debug for CountedBits<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CountedBits")
            .field("value", &format!("{:X}", self.bits))
            .field("count", &self.count)
            .field("BIT_COUNT", &P::BIT_COUNT)
            .finish()
    }
}

struct MaskedBits<'a, P: PrimitiveType> {
    bits: &'a mut P,
    offset: usize,
}

impl<'a, P: PrimitiveType> MaskedBits<'a, P> {
    fn new(bits: &'a mut P) -> Self {
        Self::with_offset(bits, 0)
    }

    fn with_offset(bits: &'a mut P, offset: usize) -> Self {
        MaskedBits { bits, offset }
    }

    fn is_full(&self) -> bool {
        self.room() == 0
    }

    fn room(&self) -> usize {
        P::BIT_COUNT - self.offset
    }

    fn set_next(&mut self, next: CountedBits<P>) {
        let mut mask = P::ZERO; // All zeros
        mask = !mask; // All ones
        if next.count >= P::BIT_COUNT {
            mask = P::ZERO; // Zero ones, followed by `next.bits` zeros
        } else {
            mask <<= next.count; // Ones, followed by `next.bits` zeros
        }
        mask = !mask; // Zeros, followed by `next.bits` ones
        mask <<= self.offset; // Zeros, followed by `next.bits` ones, followed by `self.offset` zeros
        mask = !mask; // Ones, followed by `next.bits` zeros, followed by `self.offset` ones

        *self.bits &= mask;
        *self.bits |= P::from_usize(next.bits.to_usize()) << self.offset;

        self.offset += next.count;
    }
}

impl<'a, P: PrimitiveType> Debug for MaskedBits<'a, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CountedBits")
            .field("value", &format!("{:X}", self.bits))
            .field("offset", &self.offset)
            .field("BIT_COUNT", &P::BIT_COUNT)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};
    use std::ops::Not;

    use super::{Primitive, PrimitiveType};

    #[test]
    fn immutable_contained() {
        assert!(u8::BIT_COUNT < usize::BIT_COUNT);
        assert!(u16::BIT_COUNT < usize::BIT_COUNT);

        let under: [u16; 1] = [0b_11110000_10010011];

        let u8_ref: &Primitive<u8> = Primitive::new_ref(&under, 4);
        assert_eq!(u8_ref.get(), 0b_00001001);

        assert_eq!(Primitive::<u8>::new_ref(&under, 0).get(), 0b_10010011);
        assert_eq!(Primitive::<u8>::new_ref(&under, 1).get(), 0b_01001001);
        assert_eq!(Primitive::<u8>::new_ref(&under, 2).get(), 0b_00100100);
        assert_eq!(Primitive::<u8>::new_ref(&under, 3).get(), 0b_00010010);
        assert_eq!(Primitive::<u8>::new_ref(&under, 4).get(), 0b_00001001);
        assert_eq!(Primitive::<u8>::new_ref(&under, 5).get(), 0b_10000100);
        assert_eq!(Primitive::<u8>::new_ref(&under, 6).get(), 0b_11000010);
        assert_eq!(Primitive::<u8>::new_ref(&under, 7).get(), 0b_11100001);
        assert_eq!(Primitive::<u8>::new_ref(&under, 8).get(), 0b_11110000);
    }

    #[test]
    fn immutable_across() {
        let under: [u8; 3] = [0xBA, 0xDC, 0xFE];

        let u16_ref: &Primitive<u16> = Primitive::new_ref(&under, 4);
        assert_eq!(u16_ref.get(), 0xEDCB);
    }

    #[test]
    fn mutable_contained() {
        let mut u: [u16; 1] = [0b_11110000_10010011];

        let u8_mut: &mut Primitive<u8> = Primitive::new_mut(&mut u, 4);
        let previous = u8_mut.set(0b_01011100);
        assert_eq!(previous, 0b_00001001);
        assert_eq!(u, [0b_11110101_11000011]);

        Primitive::<u8>::new_mut(&mut u, 4).modify(Not::not);
        assert_eq!(u, [0b_11111010_00110011]);
    }

    #[test]
    fn mutable_across() {
        let mut u: [u8; 3] = [0xBA, 0xDC, 0xFE];

        let u16_mut: &mut Primitive<u16> = Primitive::new_mut(&mut u, 4);
        let previous = u16_mut.set(0xBCDE);
        assert_eq!(previous, 0xEDCB);
        assert_eq!(u, [0xEA, 0xCD, 0xFB]);

        Primitive::<u16>::new_mut(&mut u, 4).modify(Not::not);
        assert_eq!(u, [0x1A, 0x32, 0xF4]);
    }

    #[test]
    fn wide_primitives() {
        assert!(u128::BIT_COUNT > usize::BIT_COUNT);
        let under: [u128; 2] = [
            0x7766554433221100FEDCBA9876543210,
            0x5444333222111000FFEEDDCCBBAA9988,
        ];

        let u128_ref: &Primitive<u128> = Primitive::new_ref(&under, 32);

        assert_eq!(u128_ref.get(), 0xBBAA99887766554433221100FEDCBA98);
    }

    #[test]
    #[should_panic(expected = "invalid bit offset")]
    fn new_ref_invalid_first_bit_index_contained() {
        let under: [u16; 1] = [0b_11110000_10010011];

        Primitive::<u8>::new_ref(&under, 9);
    }

    #[test]
    #[should_panic(expected = "invalid bit offset")]
    fn new_ref_invalid_first_bit_index_across() {
        let under: [u8; 3] = [0xBA, 0xDC, 0xFE];

        Primitive::<u16>::new_ref(&under, 9);
    }

    #[test]
    #[should_panic(expected = "invalid bit offset")]
    fn new_mut_invalid_first_bit_index_contained() {
        let mut under: [u16; 1] = [0b_11110000_10010011];

        Primitive::<u8>::new_mut(&mut under, 9);
    }

    #[test]
    #[should_panic(expected = "invalid bit offset")]
    fn new_mut_invalid_first_bit_index_across() {
        let mut under: [u8; 3] = [0xBA, 0xDC, 0xFE];

        Primitive::<u16>::new_mut(&mut under, 9);
    }

    #[test]
    fn eq() {
        let under = 0xABABu16;

        let u8_ref_0: &Primitive<u8> = Primitive::new_ref(std::slice::from_ref(&under), 0);
        let u8_ref_4: &Primitive<u8> = Primitive::new_ref(std::slice::from_ref(&under), 4);
        let u8_ref_8: &Primitive<u8> = Primitive::new_ref(std::slice::from_ref(&under), 8);

        assert!(u8_ref_0 == u8_ref_0);
        assert!(u8_ref_0 == u8_ref_8);
        // assert!(u8_ref_0 == 0xABu8); // Not possible?
        assert!(u8_ref_0 == &0xABu8);
        // assert!(0xABu8 == u8_ref_0); // Not possible?
        // assert!(&0xABu8 == u8_ref_0); // Not possible?

        assert!(u8_ref_4 != u8_ref_0);

        assert!(u8_ref_4 == u8_ref_4);
        // assert!(u8_ref_4 == 0xBAu8); // Not possible?
        assert!(u8_ref_4 == &0xBAu8);
        // assert!(0xBAu8 == u8_ref_4); // Not possible?
        // assert!(&0xBAu8 == u8_ref_4); // Not possible?
    }

    #[test]
    fn hash() {
        fn hash_value<H: Hash>(h: H) -> u64 {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            h.hash(&mut s);
            s.finish()
        }

        let under = 0xABCDu16;
        let u8_ref: &Primitive<u8> = Primitive::new_ref(std::slice::from_ref(&under), 4);

        assert_eq!(hash_value(u8_ref), hash_value(0xBCu8));
    }
}
