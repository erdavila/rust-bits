use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use linear_deque::LinearDeque;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::{BitStr, BitsPrimitive};

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

impl<U: BitsPrimitive> Default for BitString<U> {
    #[inline]
    fn default() -> Self {
        Self::new_with_underlying_type()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BitStr, BitString};

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
}
