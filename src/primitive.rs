use std::fmt::{Binary, Debug, Display, LowerExp, LowerHex, UpperExp, UpperHex};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Not, Rem, Sub};
use std::slice;

use crate::refs::{
    DstMutRefRepr, DstMutRefReprExecutor, DstRefRepr, DstRefReprExecutor, MutRefComponents,
    RefComponents,
};
use crate::{copy_bits, BitStr, PrimitiveType, UnderlyingPrimitives};

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
    pub fn new_ref<U: UnderlyingPrimitives + ?Sized>(under: &U, first_bit_index: usize) -> &Self {
        let repr = DstRefRepr::encode(under, first_bit_index, P::BIT_COUNT);
        unsafe { std::mem::transmute(repr) }
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
    pub fn new_mut<U: UnderlyingPrimitives + ?Sized>(
        under: &mut U,
        first_bit_index: usize,
    ) -> &mut Self {
        let repr = DstMutRefRepr::encode(under, first_bit_index, P::BIT_COUNT);
        unsafe { std::mem::transmute(repr) }
    }

    /// Gets the value of the referenced primitive.
    pub fn get(&self) -> P {
        struct Executor<P: PrimitiveType> {
            phantom: PhantomData<P>,
        }

        impl<P: PrimitiveType> DstRefReprExecutor<'_> for Executor<P> {
            type Output = P;

            fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output {
                let ptr = components.ptr;
                let access = PrimitiveAccess::<P, U>::new(components.offset);
                access.get_primitive(ptr)
            }
        }

        self.repr().decode_and_execute(Executor {
            phantom: PhantomData,
        })
    }

    /// Sets the value of the referenced primitive.
    ///
    /// It returns the previous value.
    pub fn set(&mut self, value: P) -> P {
        struct Executor<P: PrimitiveType> {
            value: P,
        }

        impl<P: PrimitiveType> DstMutRefReprExecutor<'_> for Executor<P> {
            type Output = P;

            fn execute<U: PrimitiveType>(self, components: MutRefComponents<U>) -> Self::Output {
                let ptr = components.ptr;
                let access = PrimitiveAccess::<P, U>::new(components.offset);
                let previous_value = access.get_primitive(ptr);
                access.set_primitive(ptr, self.value);
                previous_value
            }
        }

        self.repr_mut().decode_and_execute(Executor { value })
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
        struct Executor<P: PrimitiveType, F: FnOnce(P) -> P> {
            f: F,
            phantom: PhantomData<P>,
        }

        impl<P: PrimitiveType, F: FnOnce(P) -> P> DstMutRefReprExecutor<'_> for Executor<P, F> {
            type Output = ();

            fn execute<U: PrimitiveType>(self, components: MutRefComponents<U>) -> Self::Output {
                let ptr = components.ptr;
                let access = PrimitiveAccess::<P, U>::new(components.offset);
                let previous_value = access.get_primitive(ptr);
                let new_value = (self.f)(previous_value);
                access.set_primitive(ptr, new_value);
            }
        }

        self.repr_mut().decode_and_execute(Executor {
            f,
            phantom: PhantomData,
        });
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

impl<P: PrimitiveType> PartialEq for Primitive<P> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<P: PrimitiveType, T> PartialEq<T> for Primitive<P>
where
    P: PartialEq<T>,
{
    fn eq(&self, other: &T) -> bool {
        self.get() == *other
    }
}

impl<P: PrimitiveType> Hash for Primitive<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

impl<P: PrimitiveType> PartialOrd for Primitive<P> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: PrimitiveType, T> PartialOrd<T> for Primitive<P>
where
    P: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &T) -> Option<std::cmp::Ordering> {
        self.get().partial_cmp(other)
    }
}

impl<P: PrimitiveType> Ord for Primitive<P> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

macro_rules! impl_binary_operation {
    ($trait:ident $method:ident $operator:tt) => {
        impl<P: PrimitiveType, T> $trait<T> for &Primitive<P> where P: $trait<T> {
            type Output = <P as $trait<T>>::Output;

            fn $method(self, rhs: T) -> Self::Output {
                self.get() $operator rhs
            }
        }
    };
}

impl_binary_operation!(Add add +);
impl_binary_operation!(Sub sub -);
impl_binary_operation!(Mul mul *);
impl_binary_operation!(Div div /);
impl_binary_operation!(Rem rem %);

impl<P: PrimitiveType> Not for &Primitive<P> {
    type Output = P;

    fn not(self) -> Self::Output {
        !self.get()
    }
}
impl_binary_operation!(BitAnd bitand &);
impl_binary_operation!(BitOr bitor |);
impl_binary_operation!(BitXor bitxor ^);

macro_rules! impl_formatting {
    ($trait:ident $format:literal) => {
        impl<P: PrimitiveType> $trait for Primitive<P> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, concat!("{:", $format, "}"), self.get())
            }
        }
    };
}

impl_formatting!(Display "");
impl_formatting!(Debug "?");
impl_formatting!(Binary "b");
impl_formatting!(LowerHex "x");
impl_formatting!(UpperHex "X");
impl_formatting!(LowerExp "e");
impl_formatting!(UpperExp "E");

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

    fn get_primitive(&self, ptr: *const U) -> P {
        let slice = unsafe { slice::from_raw_parts(ptr, self.required_elems()) };
        let mut p = P::ZERO;
        copy_bits(slice, self.offset, slice::from_mut(&mut p), 0, P::BIT_COUNT);
        p
    }

    fn set_primitive(&self, ptr: *mut U, value: P) {
        let slice = unsafe { slice::from_raw_parts_mut(ptr, self.required_elems()) };
        copy_bits(slice::from_ref(&value), 0, slice, self.offset, P::BIT_COUNT);
    }

    fn required_elems(&self) -> usize {
        (self.offset + P::BIT_COUNT + U::BIT_COUNT - 1) / U::BIT_COUNT
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};
    use std::ops::Not;

    use crate::refs::{DstRefRepr, DstRefReprExecutor, RefComponents};

    use super::{Primitive, PrimitiveType};

    #[test]
    fn immutable_contained() {
        assert!(u8::BIT_COUNT < usize::BIT_COUNT);
        assert!(u16::BIT_COUNT < usize::BIT_COUNT);

        let under: u16 = 0b_11110000_10010011;

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
        let mut u: u16 = 0b_11110000_10010011;

        let u8_mut: &mut Primitive<u8> = Primitive::new_mut(&mut u, 4);
        let previous = u8_mut.set(0b_01011100);
        assert_eq!(previous, 0b_00001001);
        assert_eq!(u, 0b_11110101_11000011);

        Primitive::<u8>::new_mut(&mut u, 4).modify(Not::not);
        assert_eq!(u, 0b_11111010_00110011);
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
        let under: u16 = 0b_11110000_10010011;

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
        let mut under: u16 = 0b_11110000_10010011;

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

    #[test]
    fn ops() {
        let under = 0xABCDu16; // Bits: 1010_1011_1100_1101
        let u8_ref: &Primitive<u8> = Primitive::new_ref(std::slice::from_ref(&under), 4);

        assert!(u8_ref < &0xBDu8);
        assert!(u8_ref > &0xBBu8);

        assert_eq!(u8_ref + 0x21u8, 0xDDu8);
        assert_eq!(u8_ref - 0x12u8, 0xAAu8);
        assert_eq!(u8_ref * 1, 0xBCu8);
        assert_eq!(u8_ref / 2, 0x5Eu8);
        assert_eq!(u8_ref % 3, 0xBCu8 % 3);

        assert_eq!(!u8_ref, 0x43u8);
        assert_eq!(u8_ref & 0b10101010u8, 0b10101000u8);
        assert_eq!(u8_ref | 0b01010101u8, 0b11111101u8);
        assert_eq!(u8_ref ^ 0b10101010u8, 0b00010110u8);

        assert_eq!(format!("{:}", u8_ref), format!("{:}", 0xBCu8));
        assert_eq!(format!("{:?}", u8_ref), format!("{:?}", 0xBCu8));
        assert_eq!(format!("{:b}", u8_ref), format!("{:b}", 0xBCu8));
        assert_eq!(format!("{:x}", u8_ref), format!("{:x}", 0xBCu8));
        assert_eq!(format!("{:X}", u8_ref), format!("{:X}", 0xBCu8));
        assert_eq!(format!("{:e}", u8_ref), format!("{:e}", 0xBCu8));
        assert_eq!(format!("{:E}", u8_ref), format!("{:E}", 0xBCu8));
    }

    #[test]
    fn normalization() {
        struct Output {
            ptr: *const (),
            offset: usize,
        }

        let under: [u16; 3] = [0x7654, 0xBA98, 0xFEDC];

        let encode_and_decode_u16_ref = |first_bit_index| {
            struct Executor;

            impl DstRefReprExecutor<'_> for Executor {
                type Output = Output;

                fn execute<U: PrimitiveType>(self, components: RefComponents<U>) -> Self::Output {
                    Output {
                        ptr: components.ptr.cast(),
                        offset: components.offset,
                    }
                }
            }

            let u16_ref: &Primitive<u16> = Primitive::new_ref(&under, first_bit_index);
            let repr: DstRefRepr = unsafe { std::mem::transmute::<_, DstRefRepr>(u16_ref) };
            let output = repr.decode_and_execute(Executor);
            (u16_ref, output)
        };

        let (_, output) = encode_and_decode_u16_ref(15);
        assert!(std::ptr::eq(output.ptr as *const u16, &under[0]));
        assert_eq!(output.offset, 15);

        let (u16_ref, output) = encode_and_decode_u16_ref(16);
        assert!(std::ptr::eq(output.ptr as *const u16, &under[1]));
        assert_eq!(output.offset, 0);
        assert_eq!(u16_ref.get(), 0xBA98u16);

        let (u16_ref, output) = encode_and_decode_u16_ref(24);
        assert!(std::ptr::eq(output.ptr as *const u16, &under[1]));
        assert_eq!(output.offset, 8);
        assert_eq!(u16_ref.get(), 0xDCBAu16);
    }

    #[test]
    fn as_bit_str() {
        macro_rules! assert_type {
            ($type:ty) => {
                let under: [u8; 20] = [
                    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
                ];
                let p: &Primitive<$type> = Primitive::new_ref(&under, 3);

                let bit_str = p.as_bit_str();

                assert_eq!(bit_str.len(), <$type>::BIT_COUNT);
            };
        }

        assert_type!(usize);
        assert_type!(u8);
        assert_type!(u16);
        assert_type!(u32);
        assert_type!(u64);
        assert_type!(u128);
    }
}
