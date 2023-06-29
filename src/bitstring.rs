use linear_deque::LinearDeque;

use crate::BitsPrimitive;

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
}

impl<U: BitsPrimitive> Default for BitString<U> {
    #[inline]
    fn default() -> Self {
        Self::new_with_underlying_type()
    }
}

#[cfg(test)]
mod tests {
    use crate::BitString;

    #[test]
    fn new() {
        let string: BitString = BitString::new();

        assert_eq!(string.len(), 0);
    }
}
