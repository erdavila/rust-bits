use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use linear_deque::LinearDeque;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::utils::required_elements_for_bit_count;
use crate::{BitSource, BitStr, BitValue, BitsPrimitive};

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
    fn from_with_underlying_type<S: BitSource>(source: S) -> Self {
        let bit_count = source.bit_count();
        let buffer_elems = required_elements_for_bit_count::<U>(bit_count);

        let mut buffer = LinearDeque::new();
        buffer.resize(buffer_elems, U::ZERO);

        unsafe { source.copy_bits_to(NonNull::from(buffer.deref()).cast::<U>(), 0) };

        BitString {
            buffer,
            offset: 0,
            bit_count,
        }
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

impl<S: BitSource> From<S> for BitString<usize> {
    #[inline]
    fn from(value: S) -> Self {
        Self::from_with_underlying_type(value)
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

        let string: BitString<u8> = BitString::from_with_underlying_type(source.as_ref());

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
