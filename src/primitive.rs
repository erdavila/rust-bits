use std::fmt::Debug;
use std::marker::PhantomData;

use crate::refs::DstRefParts;
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
/// let underlying: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: 0xFEDCBA
/// let u16_ref: &Primitive<u16> = Primitive::new_ref(&underlying, 4);
/// assert_eq!(u16_ref.get(), 0xEDCBu16);
/// ```
///
/// [primitive]: PrimitiveType
#[repr(C)]
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
        assert!(
            first_bit_index + P::BIT_COUNT <= under.len() * U::BIT_COUNT,
            "invalid first bit index"
        );
        // TODO: normalize
        let parts = DstRefParts::new(&under[0], first_bit_index);
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
        assert!(
            first_bit_index + P::BIT_COUNT <= under.len() * U::BIT_COUNT,
            "invalid first bit index"
        );
        // TODO: normalize
        let parts = DstRefParts::new(&under[0], first_bit_index);
        unsafe { std::mem::transmute(parts) }
    }

    /// Gets the value of the referenced primitive.
    pub fn get(&self) -> P {
        fn get<P: PrimitiveType, U: PrimitiveType>(parts: DstRefParts) -> P {
            let ptr = parts.ptr.cast();
            let access = PrimitiveAccess::<P, U>::new(parts.bit_index());
            access.get_primitive(ptr)
        }

        let parts: DstRefParts = unsafe { std::mem::transmute(self) };

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
        let value = T::from_usize(self.bits.to_usize());
        let count = [self.count, T::BIT_COUNT, usize::BIT_COUNT]
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

#[cfg(test)]
mod tests {
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
    #[should_panic(expected = "invalid first bit index")]
    fn new_ref_invalid_first_bit_index_contained() {
        let under: [u16; 1] = [0b_11110000_10010011];

        Primitive::<u8>::new_ref(&under, 9);
    }

    #[test]
    #[should_panic(expected = "invalid first bit index")]
    fn new_ref_invalid_first_bit_index_across() {
        let under: [u8; 3] = [0xBA, 0xDC, 0xFE];

        Primitive::<u16>::new_ref(&under, 9);
    }

    #[test]
    #[should_panic(expected = "invalid first bit index")]
    fn new_mut_invalid_first_bit_index_contained() {
        let mut under: [u16; 1] = [0b_11110000_10010011];

        Primitive::<u8>::new_mut(&mut under, 9);
    }

    #[test]
    #[should_panic(expected = "invalid first bit index")]
    fn new_mut_invalid_first_bit_index_across() {
        let mut under: [u8; 3] = [0xBA, 0xDC, 0xFE];

        Primitive::<u16>::new_mut(&mut under, 9);
    }
}
