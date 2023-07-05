use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use linear_deque::{LinearDeque, SetReservedSpace};

use crate::copy_bits::{copy_bits, copy_bits_raw};
use crate::refrepr::RefRepr;
use crate::refrepr::{RefComponentsSelector, TypedRefComponents};
use crate::utils::{required_elements_for_bit_count, CountedBits};
use crate::{BitStr, BitValue, BitsPrimitive};

#[derive(Clone, Debug)]
pub struct BitString<U: BitsPrimitive = usize> {
    buffer: LinearDeque<U>,
    offset: usize,
    bit_count: usize,
}

impl BitString<usize> {
    #[inline]
    pub fn new() -> Self {
        Self::new_with_underlying_type()
    }
}

impl<U: BitsPrimitive> BitString<U> {
    #[inline]
    pub fn new_with_underlying_type() -> Self {
        BitString {
            buffer: LinearDeque::new(),
            offset: 0,
            bit_count: 0,
        }
    }

    #[inline]
    pub fn from_primitives_with_underlying_type<P: BitsPrimitive>(value: &[P]) -> Self {
        let bit_count = value.len() * P::BIT_COUNT;
        let buffer_elems = required_elements_for_bit_count::<U>(bit_count);

        let mut buffer = LinearDeque::new();
        buffer.resize(buffer_elems, U::ZERO);

        copy_bits(value, 0, &mut buffer, 0, bit_count);

        BitString {
            buffer,
            offset: 0,
            bit_count,
        }
    }

    #[inline]
    pub fn from_bitvalues_with_underlying_type(values: &[BitValue]) -> Self {
        let bit_count = values.len();
        let buffer_elems = required_elements_for_bit_count::<U>(bit_count);

        let mut buffer = LinearDeque::new();
        buffer.set_reserved_space(
            SetReservedSpace::Keep,
            SetReservedSpace::GrowTo(buffer_elems),
        );

        let mut primitive_bits = CountedBits::new();

        for bit in values.iter().copied() {
            primitive_bits.push_msb_value(bit);
            if primitive_bits.count == U::BIT_COUNT {
                buffer.push_back(primitive_bits.bits);
                primitive_bits.clear();
            }
        }

        if primitive_bits.count > 0 {
            buffer.push_back(primitive_bits.bits);
        }

        BitString {
            buffer,
            offset: 0,
            bit_count,
        }
    }

    #[inline]
    pub fn from_bit_str_with_underlying_type(bit_str: &BitStr) -> Self {
        bit_str.ref_components().select({
            struct Selector<U>(PhantomData<U>);
            impl<U: BitsPrimitive> RefComponentsSelector for Selector<U> {
                type Output = BitString<U>;

                #[inline]
                fn select<P: BitsPrimitive>(
                    self,
                    components: TypedRefComponents<P>,
                ) -> Self::Output {
                    let mut buffer = LinearDeque::new();
                    let buffer_elems = required_elements_for_bit_count::<U>(components.bit_count);

                    buffer.resize(buffer_elems, U::ZERO);
                    unsafe {
                        copy_bits_raw(
                            components.ptr.as_ptr(),
                            components.offset,
                            &mut buffer[0],
                            0,
                            components.bit_count,
                        )
                    };

                    BitString {
                        buffer,
                        offset: 0,
                        bit_count: components.bit_count,
                    }
                }
            }

            Selector::<U>(PhantomData)
        })
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.bit_count
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn as_bit_str(&self) -> &BitStr {
        let repr = self.as_repr();
        unsafe { std::mem::transmute(repr) }
    }

    #[inline]
    pub fn as_bit_str_mut(&mut self) -> &mut BitStr {
        let repr = self.as_repr();
        unsafe { std::mem::transmute(repr) }
    }

    #[inline]
    fn as_repr(&self) -> RefRepr {
        let components = TypedRefComponents {
            ptr: NonNull::from(self.buffer.deref()).cast::<U>(),
            offset: self.offset,
            bit_count: self.bit_count,
        };

        components.encode()
    }

    #[inline]
    pub fn lsb(&mut self) -> impl BitStringEnd {
        BitStringLsbEnd(self)
    }

    #[inline]
    pub fn msb(&mut self) -> impl BitStringEnd {
        BitStringMsbEnd(self)
    }
}

impl<U: BitsPrimitive> Deref for BitString<U> {
    type Target = BitStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_bit_str()
    }
}

impl<U: BitsPrimitive> DerefMut for BitString<U> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_bit_str_mut()
    }
}

impl<P: BitsPrimitive> From<&[P]> for BitString<usize> {
    #[inline]
    fn from(value: &[P]) -> Self {
        Self::from_primitives_with_underlying_type(value)
    }
}

impl From<&[BitValue]> for BitString<usize> {
    #[inline]
    fn from(values: &[BitValue]) -> Self {
        Self::from_bitvalues_with_underlying_type(values)
    }
}

impl From<&BitStr> for BitString<usize> {
    #[inline]
    fn from(bit_str: &BitStr) -> Self {
        Self::from_bit_str_with_underlying_type(bit_str)
    }
}

impl<U: BitsPrimitive> Default for BitString<U> {
    #[inline]
    fn default() -> Self {
        Self::new_with_underlying_type()
    }
}

pub trait BitStringEnd<'a> {
    fn push(&mut self, value: BitValue);
}

pub struct BitStringLsbEnd<'a, U: BitsPrimitive>(&'a mut BitString<U>);
impl<'a, U: BitsPrimitive> BitStringEnd<'a> for BitStringLsbEnd<'a, U> {
    fn push(&mut self, value: BitValue) {
        let space = self.0.offset;

        if space >= 1 {
            self.0.offset -= 1;
            if value == BitValue::One {
                self.0.buffer[0] |= U::ONE << self.0.offset;
            }
        } else {
            self.0.offset = U::BIT_COUNT - 1;
            let elem = match value {
                BitValue::Zero => U::ZERO,
                BitValue::One => U::ONE << self.0.offset,
            };
            self.0.buffer.push_front(elem);
        }

        self.0.bit_count += 1;
    }
}

pub struct BitStringMsbEnd<'a, U: BitsPrimitive>(&'a mut BitString<U>);
impl<'a, U: BitsPrimitive> BitStringEnd<'a> for BitStringMsbEnd<'a, U> {
    fn push(&mut self, value: BitValue) {
        let space = self.0.buffer.len() * U::BIT_COUNT - self.0.offset - self.0.len();

        if space >= 1 {
            if value == BitValue::One {
                let last_index = self.0.buffer.len() - 1;
                self.0.buffer[last_index] |= U::ONE << (U::BIT_COUNT - space);
            }
        } else {
            let elem = match value {
                BitValue::Zero => U::ZERO,
                BitValue::One => U::ONE,
            };
            self.0.buffer.push_back(elem);
        }

        self.0.bit_count += 1;
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use crate::BitValue::{One, Zero};
    use crate::{BitStr, BitString, BitStringEnd};

    #[test]
    fn new() {
        let string: BitString = BitString::new();

        assert_eq!(string.len(), 0);
    }

    #[test]
    fn deref() {
        let string: BitString = BitString::new();

        let str: &BitStr = &string;

        assert_eq!(str.len(), 0);
        assert!(str.is_empty());
    }

    #[test]
    fn push() {
        let mut string: BitString = BitString::new();

        string.msb().push(One); // [1]
        string.lsb().push(Zero); // 1[0]
        string.msb().push(Zero); // [0]10
        string.lsb().push(One); // 010[1]

        assert_eq!(string.len(), 4);
        assert_eq!(string.get(0), Some(One));
        assert_eq!(string.get(1), Some(Zero));
        assert_eq!(string.get(2), Some(One));
        assert_eq!(string.get(3), Some(Zero));
    }

    #[test]
    fn from_primitives_array() {
        let source: [u8; 2] = [0b10010011, 0b01101100];

        let string = BitString::from(source.as_ref());

        assert_eq!(string.deref(), BitStr::new_ref(&source));
    }

    #[test]
    fn from_bit_values_array() {
        let source = [
            One, Zero, One, One, Zero, Zero, One, One, Zero, One, One, Zero, Zero, One, One, Zero,
            One, One, Zero, Zero,
        ];

        let string: BitString<u8> = BitString::from_bitvalues_with_underlying_type(source.as_ref());

        assert_eq!(string.len(), 20);
        let mut iter = string.iter();
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(One));
        assert_eq!(iter.next(), Some(Zero));
        assert_eq!(iter.next(), Some(Zero));
        assert!(iter.next().is_none());
    }

    #[test]
    fn from_bit_str() {
        let source = BitString::from([0b10010011u8, 0b01101100u8].as_ref());

        let string = BitString::from(&source[2..14]);

        assert_eq!(string.len(), 12);
        assert_eq!(string.deref(), &source[2..14]);
    }
}
