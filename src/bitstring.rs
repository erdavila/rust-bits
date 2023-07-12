use std::iter::FusedIterator;
use std::ops::{Deref, DerefMut};

use linear_deque::LinearDeque;

use crate::copy_bits::copy_bits_ptr;
use crate::iter::BitIterator;
use crate::refrepr::{BitPointer, Offset, RefRepr, TypedRefComponents};
use crate::utils::{required_elements_for_bit_count, CountedBits};
use crate::{BitAccessor, BitSource, BitStr, BitValue, BitsPrimitive, PrimitiveAccessor};

#[derive(Clone, Debug)]
pub struct BitString<U: BitsPrimitive = usize> {
    buffer: LinearDeque<U>,
    offset: Offset<U>,
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
            offset: Offset::new(0),
            bit_count: 0,
        }
    }

    #[inline]
    fn from_with_underlying_type<S: BitSource>(source: S) -> Self {
        let bit_count = source.bit_count();
        let buffer_elems = required_elements_for_bit_count::<U>(bit_count);

        let mut buffer = LinearDeque::new();
        buffer.resize(buffer_elems, U::ZERO);

        unsafe { source.copy_bits_to(buffer.as_ref().into(), 0) };

        BitString {
            buffer,
            offset: Offset::new(0),
            bit_count,
        }
    }

    #[inline]
    fn from_bit_values_iter_with_underlying_type<T: IntoIterator<Item = BitValue>>(
        iter: T,
    ) -> Self {
        let mut buffer = LinearDeque::new();
        let mut primitive_bits = CountedBits::new();

        for bit in iter.into_iter() {
            primitive_bits.push_msb_value(bit);
            if primitive_bits.is_full() {
                buffer.push_back(primitive_bits.bits);
                primitive_bits.clear();
            }
        }

        let mut bit_count = buffer.len() * U::BIT_COUNT;

        if primitive_bits.count > 0 {
            bit_count += primitive_bits.count;
            buffer.push_back(primitive_bits.bits);
        }

        BitString {
            buffer,
            offset: Offset::new(0),
            bit_count,
        }
    }

    #[inline]
    fn from_primitives_iter_with_underlying_type<P: BitsPrimitive, T: IntoIterator<Item = P>>(
        iter: T,
    ) -> Self {
        let mut bit_string = Self::new_with_underlying_type();
        for primitive in iter {
            bit_string.msb().push(primitive);
        }
        bit_string
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
            bit_ptr: BitPointer::new(self.buffer.as_ref().into(), self.offset),
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

impl<U: BitsPrimitive> AsRef<BitStr> for BitString<U> {
    #[inline]
    fn as_ref(&self) -> &BitStr {
        self.as_bit_str()
    }
}

impl<U: BitsPrimitive> AsMut<BitStr> for BitString<U> {
    #[inline]
    fn as_mut(&mut self) -> &mut BitStr {
        self.as_bit_str_mut()
    }
}

impl<S: BitSource> From<S> for BitString<usize> {
    #[inline]
    fn from(value: S) -> Self {
        Self::from_with_underlying_type(value)
    }
}

impl FromIterator<BitValue> for BitString<usize> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = BitValue>>(iter: T) -> Self {
        Self::from_bit_values_iter_with_underlying_type(iter)
    }
}

impl<P: BitsPrimitive> FromIterator<P> for BitString<usize> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = P>>(iter: T) -> Self {
        Self::from_primitives_iter_with_underlying_type(iter)
    }
}

impl<U: BitsPrimitive> IntoIterator for BitString<U> {
    type Item = BitValue;

    type IntoIter = IntoIter<U>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            buffer: self.buffer,
            start_offset: self.offset.value(),
            end_offset: self.offset.value() + self.bit_count,
        }
    }
}

impl<U: BitsPrimitive> Default for BitString<U> {
    #[inline]
    fn default() -> Self {
        Self::new_with_underlying_type()
    }
}

pub trait BitStringEnd<'a> {
    fn push<S: BitSource>(&mut self, source: S);
}

pub struct BitStringLsbEnd<'a, U: BitsPrimitive>(&'a mut BitString<U>);
impl<'a, U: BitsPrimitive> BitStringEnd<'a> for BitStringLsbEnd<'a, U> {
    fn push<S: BitSource>(&mut self, source: S) {
        let pushed_bits_count = source.bit_count();
        let space = self.0.offset.value();

        let mut updated_offset = self.0.offset.value();
        if let Some(additional_elems_bit_count) = pushed_bits_count.checked_sub(space) {
            let additional_elems = required_elements_for_bit_count::<U>(additional_elems_bit_count);
            self.0
                .buffer
                .resize_at_front(self.0.buffer.len() + additional_elems, U::ZERO);
            updated_offset += additional_elems * U::BIT_COUNT;
        }
        updated_offset -= pushed_bits_count;

        self.0.offset = Offset::new(updated_offset);
        unsafe { source.copy_bits_to(self.0.buffer.as_ref().into(), updated_offset) };
        self.0.bit_count += pushed_bits_count;
    }
}

pub struct BitStringMsbEnd<'a, U: BitsPrimitive>(&'a mut BitString<U>);
impl<'a, U: BitsPrimitive> BitStringEnd<'a> for BitStringMsbEnd<'a, U> {
    fn push<S: BitSource>(&mut self, source: S) {
        let pushed_bits_count = source.bit_count();
        let space = self.0.buffer.len() * U::BIT_COUNT - self.0.offset.value() - self.0.len();

        if let Some(additional_elems_bit_count) = pushed_bits_count.checked_sub(space) {
            let additional_elems = required_elements_for_bit_count::<U>(additional_elems_bit_count);
            self.0
                .buffer
                .resize_at_back(self.0.buffer.len() + additional_elems, U::ZERO);
        }

        unsafe {
            source.copy_bits_to(
                self.0.buffer.as_ref().into(),
                self.0.offset.value() + self.0.bit_count,
            )
        };
        self.0.bit_count += pushed_bits_count;
    }
}

pub struct IntoIter<U> {
    buffer: LinearDeque<U>,
    start_offset: usize,
    end_offset: usize,
}
impl<U: BitsPrimitive> IntoIter<U> {
    #[inline]
    fn bit_count(&self) -> usize {
        self.end_offset - self.start_offset
    }

    #[inline]
    fn next_at_front(&mut self, bit_count: usize) -> Option<IntoIterNextItemParams<U>> {
        (bit_count <= self.bit_count()).then(|| {
            let ptr = self.buffer.as_ref().into();
            let bit_ptr = BitPointer::new_normalized(ptr, self.start_offset);
            self.start_offset += bit_count;
            IntoIterNextItemParams { bit_ptr, bit_count }
        })
    }

    #[inline]
    fn next_at_back(&mut self, bit_count: usize) -> Option<IntoIterNextItemParams<U>> {
        (bit_count <= self.bit_count()).then(|| {
            let ptr = self.buffer.as_ref().into();
            self.end_offset -= bit_count;
            let bit_ptr = BitPointer::new_normalized(ptr, self.end_offset);
            IntoIterNextItemParams { bit_ptr, bit_count }
        })
    }

    #[inline]
    fn get_bit_value(params: IntoIterNextItemParams<U>) -> BitValue {
        let accessor = BitAccessor::new(params.bit_ptr);
        accessor.get()
    }

    #[inline]
    fn get_primitive<P: BitsPrimitive>(params: IntoIterNextItemParams<U>) -> P {
        let accessor = PrimitiveAccessor::<P, _>::new(params.bit_ptr);
        accessor.get()
    }

    #[inline]
    fn get_slice(params: IntoIterNextItemParams<U>) -> BitString<U> {
        let buffer_elems = required_elements_for_bit_count::<U>(params.bit_count);
        let mut buffer = LinearDeque::new();
        buffer.resize(buffer_elems, U::ZERO);

        let src = params.bit_ptr;
        let dst = BitPointer::new_normalized(buffer.as_mut().into(), 0);
        unsafe {
            copy_bits_ptr(src, dst, params.bit_count);
        }

        BitString {
            buffer,
            offset: Offset::new(0),
            bit_count: params.bit_count,
        }
    }
}
impl<U: BitsPrimitive> Iterator for IntoIter<U> {
    type Item = BitValue;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.bit_count();
        (len, Some(len))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.next_at_front(1).map(Self::get_bit_value)
    }
}
impl<U: BitsPrimitive> DoubleEndedIterator for IntoIter<U> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_at_back(1).map(Self::get_bit_value)
    }
}
impl<'a, U: BitsPrimitive> BitIterator<'a> for IntoIter<U> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = P;

    type SliceItem = BitString<U>;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.next_at_front(P::BIT_COUNT).map(Self::get_primitive)
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.next_at_back(P::BIT_COUNT).map(Self::get_primitive)
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.next_at_front(len).map(Self::get_slice)
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.next_at_back(len).map(Self::get_slice)
    }
}
impl<U: BitsPrimitive> ExactSizeIterator for IntoIter<U> {}
impl<U: BitsPrimitive> FusedIterator for IntoIter<U> {}

struct IntoIterNextItemParams<U: BitsPrimitive> {
    bit_ptr: BitPointer<U>,
    bit_count: usize,
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use crate::iter::BitIterator;
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
    fn as_ref() {
        let string = BitString::from([0b10010011u8].as_ref());

        let str: &BitStr = string.as_ref();

        assert_eq!(str, &[One, One, Zero, Zero, One, Zero, Zero, One]);
    }

    #[test]
    fn as_mut() {
        let mut string = BitString::from([0b10010011u8].as_ref());

        let str: &mut BitStr = string.as_mut();

        assert_eq!(str, &[One, One, Zero, Zero, One, Zero, Zero, One]);
    }

    #[test]
    fn push() {
        let mut string: BitString = BitString::new();

        string.msb().push(One); // [1]
        string.lsb().push(0b10010011u8); // 1[10010011]
        string.msb().push(&BitString::from(Zero)); // [0]110010011
        string.lsb().push(Zero); // 0110010011[0]
        string.msb().push(0b01101100u8); // [01101100]01100100110
        string.lsb().push(&BitString::from(One)); // 0110110001100100110[1]

        assert_eq!(string.len(), 20);
        assert_eq!(
            string.deref(),
            &[
                One, Zero, One, One, Zero, Zero, One, Zero, Zero, One, One, Zero, Zero, Zero, One,
                One, Zero, One, One, Zero
            ]
        );
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

    #[test]
    fn from_other_types() {
        let string = BitString::from(One);
        assert_eq!(string.len(), 1);
        assert_eq!(string[0].read(), One);

        let string = BitString::from([One]);
        assert_eq!(string.len(), 1);
        assert_eq!(string[0].read(), One);

        let string = BitString::from(0b10010011u8);
        assert_eq!(string.len(), 8);
        assert_eq!(string.deref(), BitStr::new_ref(&[0b10010011u8]));

        let string = BitString::from([0b10010011u8]);
        assert_eq!(string.len(), 8);
        assert_eq!(string.deref(), BitStr::new_ref(&[0b10010011u8]));

        let string = BitString::from(BitString::from(One));
        assert_eq!(string.len(), 1);
        assert_eq!(string[0].read(), One);

        let string = BitString::from(&BitString::from(One));
        assert_eq!(string.len(), 1);
        assert_eq!(string[0].read(), One);
    }

    #[test]
    fn from_iter_bit_values() {
        let source = &BitString::from([0b10010011u8, 0b01101100u8])[2..14];

        let bit_string = BitString::from_iter(source.iter());

        assert_eq!(bit_string.len(), 12);
        assert_eq!(bit_string.deref(), source);
    }

    #[test]
    fn from_iter_primitives() {
        let bits = [0b10010011u8, 0b01101100u8];

        let bit_string = BitString::from_iter(bits.into_iter());

        assert_eq!(bit_string.len(), 16);
        assert_eq!(bit_string.deref(), BitStr::new_ref(&bits));
    }

    #[test]
    fn into_iter() {
        let memory: [u16; 3] = [0xDCBA, 0x54FE, 0x9876]; // In memory: 987654FEDCBA
        let bit_str = BitStr::new_ref(&memory);
        let bit_string = BitString::from(&bit_str[4..44]); // 87654FEDCB

        let mut iter = bit_string.into_iter();

        assert_eq!(iter.len(), 40); // [87654FEDCB]
        {
            let bit_value: Option<crate::BitValue> = iter.next();
            assert_eq!(bit_value.unwrap(), One); // B: 101[1]
        }
        assert_eq!(iter.next().unwrap(), One); // B: 10[1]1
        assert_eq!(iter.next().unwrap(), Zero); // B: 1[0]11
        assert_eq!(iter.next().unwrap(), One); // B: [1]011
        assert_eq!(iter.len(), 36); // [87654FEDC]B
        {
            let primitive: Option<u16> = iter.next_primitive::<u16>();
            assert_eq!(primitive.unwrap(), 0xFEDC);
        }
        assert_eq!(iter.len(), 20); // [87654]FEDCB
        {
            let bit_string: Option<BitString> = iter.next_n(4);
            assert_eq!(bit_string.unwrap().as_ref(), &[Zero, Zero, One, Zero]); // 4: 0100
        }
        assert_eq!(iter.len(), 16); // [8765]4FEDCB
        assert_eq!(iter.next_back().unwrap(), One); // 8: [1]000
        assert_eq!(iter.next_back().unwrap(), Zero); // 8: 1[0]00
        assert_eq!(iter.next_back().unwrap(), Zero); // 8: 10[0]0
        assert_eq!(iter.next_back().unwrap(), Zero); // 8: 100[0]
        assert_eq!(iter.len(), 12); // 8[765]4FEDCB
        assert_eq!(iter.next_primitive_back::<u8>().unwrap(), 0x76);
        assert_eq!(iter.len(), 4); // 876[5]4FEDCB
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert!(iter.next_n_back(5).is_none());
        assert_eq!(
            iter.next_n_back(4).unwrap().as_ref(),
            &[One, Zero, One, Zero]
        ); // 5: 0101
        assert_eq!(iter.len(), 0); // 8765[]4FEDCB
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap().as_ref(), &[]);
        assert_eq!(iter.next_n_back(0).unwrap().as_ref(), &[]);
    }
}
