use std::fmt::{Binary, Debug, Display, LowerHex, UpperHex};
use std::iter::FusedIterator;
use std::ops::{Deref, DerefMut};
use std::slice;
use std::str::FromStr;

use linear_deque::LinearDeque;

use crate::copy_bits::copy_bits_ptr;
use crate::iter::BitIterator;
use crate::refrepr::{BitPointer, Offset, RefRepr, TypedRefComponents};
use crate::utils::{required_elements_for_bit_count, CountedBits};
use crate::{BitAccessor, BitSource, BitStr, BitValue, BitsPrimitive, PrimitiveAccessor};

#[derive(Clone)]
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

impl<U: BitsPrimitive> FromStr for BitString<U> {
    type Err = BitStringParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut bit_string = BitString::new_with_underlying_type();

        #[inline]
        fn push_bits<U: BitsPrimitive>(value: CountedBits<u8>, bit_string: &mut BitString<U>) {
            let bit_str = &BitStr::new_ref(slice::from_ref(&value.bits))[0..value.count];
            bit_string.lsb().push(bit_str)
        }

        #[derive(Clone, Copy)]
        enum Base {
            Bin,
            Hex,
        }

        impl Base {
            #[inline]
            fn parse_digit(&self, ch: char) -> Result<CountedBits<u8>, char> {
                match self {
                    Base::Bin => {
                        let value = match ch {
                            '0' | '1' => (ch as u8) - b'0',
                            _ => return Err(ch),
                        };
                        Ok(CountedBits::with_count(value, 1))
                    }
                    Base::Hex => {
                        let value = match ch {
                            'a'..='f' => (ch as u8) - b'a' + 10,
                            'A'..='F' => (ch as u8) - b'A' + 10,
                            '0'..='9' => (ch as u8) - b'0',
                            _ => return Err(ch),
                        };
                        Ok(CountedBits::with_count(value, 4))
                    }
                }
            }

            #[inline]
            fn other(&self) -> Self {
                match self {
                    Base::Bin => Base::Hex,
                    Base::Hex => Base::Bin,
                }
            }
        }

        enum State {
            Expect(Base),
            ExpectZeroFound(Base, CountedBits<u8>),
            Group(Base),
        }

        let mut state = State::Expect(Base::Bin);

        for (index, ch) in s.chars().enumerate() {
            match state {
                State::Expect(base) => match base.parse_digit(ch) {
                    Ok(value) if ch == '0' => state = State::ExpectZeroFound(base, value),
                    Ok(value) => {
                        push_bits(value, &mut bit_string);
                        state = State::Group(base);
                    }
                    Err('_') => state = State::Group(base),
                    Err(':') => state = State::Expect(base.other()),
                    _ => return Err(BitStringParseError(index)),
                },
                State::ExpectZeroFound(base, digit_zero_value) => match base.parse_digit(ch) {
                    _ if ch == 'b' => state = State::Group(Base::Bin),
                    _ if ch == 'x' => state = State::Group(Base::Hex),
                    Ok(value) => {
                        push_bits(digit_zero_value, &mut bit_string);
                        push_bits(value, &mut bit_string);
                        state = State::Group(base);
                    }
                    Err('_') => {
                        push_bits(digit_zero_value, &mut bit_string);
                        state = State::Group(base);
                    }
                    Err(':') => {
                        push_bits(digit_zero_value, &mut bit_string);
                        state = State::Expect(base.other());
                    }
                    _ => return Err(BitStringParseError(index)),
                },
                State::Group(base) => match base.parse_digit(ch) {
                    Ok(value) => push_bits(value, &mut bit_string),
                    Err('_') => (),
                    Err(':') => state = State::Expect(base.other()),
                    _ => return Err(BitStringParseError(index)),
                },
            }
        }

        if let State::ExpectZeroFound(_, digit_zero_value) = state {
            push_bits(digit_zero_value, &mut bit_string);
        }

        Ok(bit_string)
    }
}

impl<U: BitsPrimitive> Display for BitString<U> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.as_ref(), f)
    }
}

impl<U: BitsPrimitive> Binary for BitString<U> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Binary::fmt(self.as_ref(), f)
    }
}

impl<U: BitsPrimitive> LowerHex for BitString<U> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        LowerHex::fmt(self.as_ref(), f)
    }
}

impl<U: BitsPrimitive> UpperHex for BitString<U> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        UpperHex::fmt(self.as_ref(), f)
    }
}

impl<U: BitsPrimitive> Debug for BitString<U> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.as_ref(), f)
    }
}

#[derive(Debug)]
pub struct BitStringParseError(usize);
impl BitStringParseError {
    #[inline]
    pub fn index(&self) -> usize {
        self.0
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

    #[test]
    fn from_str() {
        macro_rules! assert_ok {
            ($str:literal, $expected_bits:expr) => {
                let parsed = $str.parse::<BitString>().unwrap();
                assert_eq!(parsed.as_ref(), &$expected_bits);
            };
        }

        macro_rules! assert_err {
            ($str:literal, $expected_index:expr) => {
                let err = $str.parse::<BitString>().unwrap_err();
                assert_eq!(err.index(), $expected_index);
            };
        }

        assert_ok!("", []);
        assert_ok!(":", []);
        assert_ok!("::", []);
        assert_ok!("10", [Zero, One]);
        assert_ok!("001", [One, Zero, Zero]);
        assert_ok!("01", [One, Zero]);
        assert_ok!("0b", []);
        assert_ok!("0b10", [Zero, One]);
        assert_ok!("0b01", [One, Zero]);
        assert_ok!("0b_1_0_", [Zero, One]);
        assert_ok!("0b_0_1_", [One, Zero]);
        assert_ok!("_1_0_", [Zero, One]);
        assert_ok!("_0_1_", [One, Zero]);
        assert_ok!("0_1_", [One, Zero]);
        assert_ok!("0:F", [One, One, One, One, Zero]);
        assert_ok!("0x", []);
        assert_ok!("0xa", [Zero, One, Zero, One]);
        assert_ok!("0x_a", [Zero, One, Zero, One]);
        assert_ok!("0xa_", [Zero, One, Zero, One]);
        assert_ok!("0:_a", [Zero, One, Zero, One, Zero]);
        assert_ok!("1:0", [Zero, Zero, Zero, Zero, One]);
        assert_ok!(
            "101:aB",
            [One, One, Zero, One, Zero, One, Zero, One, One, Zero, One]
        );
        assert_ok!(
            "0b101:0xaB",
            [One, One, Zero, One, Zero, One, Zero, One, One, Zero, One]
        );
        assert_ok!(
            "0xaB:0b101",
            [One, Zero, One, One, One, Zero, One, Zero, One, Zero, One]
        );
        assert_ok!(
            "0xaB:101",
            [One, Zero, One, One, One, Zero, One, Zero, One, Zero, One]
        );
        assert_ok!("100:0b10011", [One, One, Zero, Zero, One, Zero, Zero, One]);
        assert_ok!("0xB::A", [Zero, One, Zero, One, One, One, Zero, One]);
        assert_ok!("1::1", [One, One]);
        assert_ok!(
            "1:00",
            [Zero, Zero, Zero, Zero, Zero, Zero, Zero, Zero, One]
        );
        assert_ok!("1:0a", [Zero, One, Zero, One, Zero, Zero, Zero, Zero, One]);
        assert_ok!("1:0_a", [Zero, One, Zero, One, Zero, Zero, Zero, Zero, One]);
        assert_ok!("1:0:1", [One, Zero, Zero, Zero, Zero, One]);

        assert_err!("0a", 1);
        assert_err!("1b", 1);
        assert_err!("1x", 1);
        assert_err!("1:x:", 2);
        assert_err!("0xBx", 3);
        assert_err!("0xB:x", 4);
        assert_err!("0xB:b", 4);
    }

    #[test]
    fn formatting() {
        let bit_string = BitString::from(0b01101100u8);

        assert_eq!(format!("{bit_string}"), "01101100");
        assert_eq!(format!("{bit_string:#}"), "0b01101100");
        assert_eq!(format!("{bit_string:b}"), "01101100");
        assert_eq!(format!("{bit_string:#b}"), "0b01101100");
        assert_eq!(format!("{bit_string:x}"), "6c");
        assert_eq!(format!("{bit_string:#x}"), "0x6c");
        assert_eq!(format!("{bit_string:X}"), "6C");
        assert_eq!(format!("{bit_string:#X}"), "0x6C");
        assert_eq!(format!("{bit_string:?}"), "\"01101100\"");
        assert_eq!(format!("{bit_string:#?}"), "\"0b01101100\"");

        let bit_string = BitString::from(&bit_string[0..7]);

        assert_eq!(format!("{bit_string}"), "1101100");
        assert_eq!(format!("{bit_string:#}"), "0b1101100");
        assert_eq!(format!("{bit_string:b}"), "1101100");
        assert_eq!(format!("{bit_string:#b}"), "0b1101100");
        assert_eq!(format!("{bit_string:x}"), "110:c");
        assert_eq!(format!("{bit_string:#x}"), "0b110:0xc");
        assert_eq!(format!("{bit_string:X}"), "110:C");
        assert_eq!(format!("{bit_string:#X}"), "0b110:0xC");
        assert_eq!(format!("{bit_string:?}"), "\"1101100\"");
        assert_eq!(format!("{bit_string:#?}"), "\"0b1101100\"");
    }

    #[test]
    fn formatting_and_parsing() {
        macro_rules! assert_format {
            ($bit_string:expr, $format:literal, $expected_formatted:literal) => {{
                let formatted = format!(concat!("{", $format, "}"), $bit_string);
                let parsed = formatted.parse::<BitString>();

                assert_eq!(formatted, $expected_formatted);
                assert_eq!(parsed.unwrap().as_ref(), $bit_string.as_ref());
            }};
        }

        let bit_string = BitString::from(0b01101100u8);

        assert_format!(bit_string, "", "01101100");
        assert_format!(bit_string, ":#", "0b01101100");
        assert_format!(bit_string, ":b", "01101100");
        assert_format!(bit_string, ":#b", "0b01101100");
        // assert_format!(bit_string, ":x", "6c"); // "0x" is required for parsing
        assert_format!(bit_string, ":#x", "0x6c");
        // assert_format!(bit_string, ":X", "6C"); // "0x" is required for parsing
        assert_format!(bit_string, ":#X", "0x6C");

        let bit_string = BitString::from(&bit_string[0..7]);

        assert_format!(bit_string, "", "1101100");
        assert_format!(bit_string, ":#", "0b1101100");
        assert_format!(bit_string, ":b", "1101100");
        assert_format!(bit_string, ":#b", "0b1101100");
        assert_format!(bit_string, ":x", "110:c");
        assert_format!(bit_string, ":#x", "0b110:0xc");
        assert_format!(bit_string, ":X", "110:C");
        assert_format!(bit_string, ":#X", "0b110:0xC");
    }
}
