use std::borrow::{Borrow, BorrowMut};
use std::fmt::{Binary, Debug, Display, LowerHex, UpperHex};
use std::hash::Hash;
use std::iter::FusedIterator;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::slice;
use std::str::FromStr;

use linear_deque::LinearDeque;

use crate::copy_bits::copy_bits_ptr;
use crate::iter::BitIterator;
use crate::refrepr::{BitPointer, Offset, RefRepr, TypedPointer, TypedRefComponents};
use crate::utils::primitive_elements_regions::PrimitiveElementsRegions;
use crate::utils::{
    required_primitive_elements_for_type, required_primitive_elements_typed, CountedBits,
};
use crate::{BitAccessor, BitSource, BitStr, BitValue, BitsPrimitive, PrimitiveAccessor};

#[derive(Clone)]
pub struct BitString {
    buffer: LinearDeque<u8>,
    offset: Offset<u8>,
    bit_count: usize,
}

impl BitString {
    #[inline]
    pub fn new() -> Self {
        BitString {
            buffer: LinearDeque::new(),
            offset: Offset::new(0),
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
            bit_ptr: BitPointer::new(self.buffer.as_ref().into(), self.offset),
            bit_count: self.bit_count,
        };

        components.encode()
    }

    #[inline]
    fn primitive_elements_regions(&self) -> PrimitiveElementsRegions {
        PrimitiveElementsRegions::new(self.offset.value(), self.bit_count, u8::BIT_COUNT)
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

impl Deref for BitString {
    type Target = BitStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_bit_str()
    }
}

impl DerefMut for BitString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_bit_str_mut()
    }
}

impl AsRef<BitStr> for BitString {
    #[inline]
    fn as_ref(&self) -> &BitStr {
        self.as_bit_str()
    }
}

impl AsMut<BitStr> for BitString {
    #[inline]
    fn as_mut(&mut self) -> &mut BitStr {
        self.as_bit_str_mut()
    }
}

impl Borrow<BitStr> for BitString {
    #[inline]
    fn borrow(&self) -> &BitStr {
        self.as_bit_str()
    }
}

impl BorrowMut<BitStr> for BitString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut BitStr {
        self.as_bit_str_mut()
    }
}

impl<S: BitSource> From<S> for BitString {
    #[inline]
    fn from(source: S) -> Self {
        let bit_count = source.bit_count();
        let buffer_elems = required_primitive_elements_for_type::<u8>(0, bit_count);

        let mut buffer = LinearDeque::new();
        buffer.resize(buffer_elems, 0u8);

        unsafe { source.copy_bits_to(buffer.as_ref().into(), 0) };

        BitString {
            buffer,
            offset: Offset::new(0),
            bit_count,
        }
    }
}

impl FromIterator<BitValue> for BitString {
    #[inline]
    fn from_iter<T: IntoIterator<Item = BitValue>>(iter: T) -> Self {
        let mut buffer = LinearDeque::new();
        let mut primitive_bits = CountedBits::new();

        for bit in iter.into_iter() {
            primitive_bits.push_msb_value(bit);
            if primitive_bits.is_full() {
                buffer.push_back(primitive_bits.bits);
                primitive_bits.clear();
            }
        }

        let mut bit_count = buffer.len() * u8::BIT_COUNT;

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
}

impl<P: BitsPrimitive> FromIterator<P> for BitString {
    #[inline]
    fn from_iter<T: IntoIterator<Item = P>>(iter: T) -> Self {
        let mut bit_string = BitString::new();
        for primitive in iter {
            bit_string.msb().push(primitive);
        }
        bit_string
    }
}

impl IntoIterator for BitString {
    type Item = BitValue;

    type IntoIter = IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            buffer: self.buffer,
            start_offset: self.offset.value(),
            end_offset: self.offset.value() + self.bit_count,
        }
    }
}

impl Eq for BitString {}

impl PartialEq<BitString> for BitString {
    #[inline]
    fn eq(&self, other: &BitString) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl PartialEq<&BitStr> for BitString {
    #[inline]
    fn eq(&self, other: &&BitStr) -> bool {
        self.as_ref() == *other
    }
}

impl PartialEq<&mut BitStr> for BitString {
    #[inline]
    fn eq(&self, other: &&mut BitStr) -> bool {
        self.as_ref() == *other
    }
}

impl PartialEq<BitString> for &BitStr {
    #[inline]
    fn eq(&self, other: &BitString) -> bool {
        *self == other.as_ref()
    }
}

impl PartialEq<BitString> for &mut BitStr {
    #[inline]
    fn eq(&self, other: &BitString) -> bool {
        *self == other.as_ref()
    }
}

impl<S: AsRef<[BitValue]>> PartialEq<S> for BitString {
    #[inline]
    fn eq(&self, other: &S) -> bool {
        self.as_ref().eq_slice(other.as_ref())
    }
}

impl<const N: usize> PartialEq<BitString> for [BitValue; N] {
    #[inline]
    fn eq(&self, other: &BitString) -> bool {
        *other == *self
    }
}

impl PartialEq<BitString> for Vec<BitValue> {
    #[inline]
    fn eq(&self, other: &BitString) -> bool {
        *other == *self
    }
}

impl PartialOrd<BitString> for BitString {
    #[inline]
    fn partial_cmp(&self, other: &BitString) -> Option<std::cmp::Ordering> {
        self.as_bit_str().partial_cmp(other.as_bit_str())
    }
}

impl PartialOrd<&BitStr> for BitString {
    #[inline]
    fn partial_cmp(&self, other: &&BitStr) -> Option<std::cmp::Ordering> {
        self.as_bit_str().partial_cmp(other)
    }
}

impl PartialOrd<&mut BitStr> for BitString {
    #[inline]
    fn partial_cmp(&self, other: &&mut BitStr) -> Option<std::cmp::Ordering> {
        self.as_bit_str().partial_cmp(other)
    }
}

impl PartialOrd<BitString> for &BitStr {
    #[inline]
    fn partial_cmp(&self, other: &BitString) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.as_bit_str())
    }
}

impl PartialOrd<BitString> for &mut BitStr {
    #[inline]
    fn partial_cmp(&self, other: &BitString) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.as_bit_str())
    }
}

impl Hash for BitString {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state);
    }
}

impl Default for BitString {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl FromStr for BitString {
    type Err = BitStringParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut bit_string = BitString::new();

        #[inline]
        fn push_bits(value: CountedBits<u8>, bit_string: &mut BitString) {
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

impl Display for BitString {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.as_ref(), f)
    }
}

impl Binary for BitString {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Binary::fmt(self.as_ref(), f)
    }
}

impl LowerHex for BitString {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        LowerHex::fmt(self.as_ref(), f)
    }
}

impl UpperHex for BitString {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        UpperHex::fmt(self.as_ref(), f)
    }
}

impl Debug for BitString {
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
    fn pop(&mut self) -> Option<BitValue>;
    fn pop_primitive<P: BitsPrimitive>(&mut self) -> Option<P>;
    fn pop_n(&mut self, bit_count: usize) -> Option<BitString>;

    #[inline]
    fn pop_up_to(&mut self, bit_count: usize) -> BitString {
        match self.pop_n(bit_count) {
            Some(bit_string) => bit_string,
            None => {
                let mut bit_string = BitString::new();
                mem::swap(self.bit_string(), &mut bit_string);
                bit_string
            }
        }
    }

    fn bit_string(&mut self) -> &mut BitString;
}

pub struct BitStringLsbEnd<'a>(&'a mut BitString);
impl<'a> BitStringLsbEnd<'a> {
    fn pop_bits<R>(&mut self, bit_count: usize, f: fn(BitPointer<u8>, usize) -> R) -> Option<R> {
        (bit_count <= self.0.bit_count).then(|| {
            let bit_ptr = BitPointer::new(TypedPointer::from(self.0.buffer.deref()), self.0.offset);
            let value = f(bit_ptr, bit_count);

            let mut bits_to_discard = bit_count;
            match self.0.primitive_elements_regions() {
                PrimitiveElementsRegions::Multiple {
                    lsb_element,
                    full_elements,
                    msb_element,
                } => 'elem_discard: {
                    if let Some(lsb) = lsb_element {
                        if lsb.bit_count <= bits_to_discard {
                            self.0.buffer.pop_front();
                            bits_to_discard -= lsb.bit_count;
                        } else {
                            break 'elem_discard;
                        }
                    }

                    if let Some(full) = full_elements {
                        for _ in full.indexes {
                            if u8::BIT_COUNT <= bits_to_discard {
                                self.0.buffer.pop_front();
                                bits_to_discard -= u8::BIT_COUNT;
                            } else {
                                break 'elem_discard;
                            }
                        }
                    }

                    if let Some(msb) = msb_element {
                        if msb.bit_count == bits_to_discard {
                            self.0.buffer.pop_front();
                        } else {
                            break 'elem_discard;
                        }
                    }
                }
                PrimitiveElementsRegions::Single {
                    bit_offset: _,
                    bit_count,
                } => {
                    if bit_count == bits_to_discard {
                        self.0.buffer.pop_front();
                    }
                }
            }

            self.0.offset = Offset::new(self.0.offset.value() + bit_count);
            self.0.bit_count -= bit_count;

            value
        })
    }
}
impl<'a> BitStringEnd<'a> for BitStringLsbEnd<'a> {
    fn push<S: BitSource>(&mut self, source: S) {
        let pushed_bits_count = source.bit_count();
        let space = self.0.offset.value();

        let mut updated_offset = self.0.offset.value();
        if let Some(additional_elems_bit_count) = pushed_bits_count.checked_sub(space) {
            let additional_elems =
                required_primitive_elements_for_type::<u8>(0, additional_elems_bit_count);
            self.0
                .buffer
                .resize_at_front(self.0.buffer.len() + additional_elems, 0u8);
            updated_offset += additional_elems * u8::BIT_COUNT;
        }
        updated_offset -= pushed_bits_count;

        self.0.offset = Offset::new(updated_offset);
        unsafe { source.copy_bits_to(self.0.buffer.as_ref().into(), updated_offset) };
        self.0.bit_count += pushed_bits_count;
    }

    #[inline]
    fn pop(&mut self) -> Option<BitValue> {
        self.pop_bits(1, get_bit_value_from_bit_str)
    }

    #[inline]
    fn pop_primitive<P: BitsPrimitive>(&mut self) -> Option<P> {
        self.pop_bits(P::BIT_COUNT, get_primitive_from_bit_str)
    }

    #[inline]
    fn pop_n(&mut self, bit_count: usize) -> Option<BitString> {
        self.pop_bits(bit_count, get_bit_string_from_bit_str)
    }

    #[inline]
    fn bit_string(&mut self) -> &mut BitString {
        self.0
    }
}

pub struct BitStringMsbEnd<'a>(&'a mut BitString);
impl<'a> BitStringMsbEnd<'a> {
    fn pop_bits<R>(&mut self, bit_count: usize, f: fn(BitPointer<u8>, usize) -> R) -> Option<R> {
        (bit_count <= self.0.bit_count).then(|| {
            let bit_ptr = BitPointer::new_normalized(
                TypedPointer::from(self.0.buffer.deref()),
                self.0.offset.value() + self.0.bit_count - bit_count,
            );
            let value = f(bit_ptr, bit_count);

            let mut bits_to_discard = bit_count;
            match self.0.primitive_elements_regions() {
                PrimitiveElementsRegions::Multiple {
                    lsb_element,
                    full_elements,
                    msb_element,
                } => 'elem_discard: {
                    if let Some(msb) = msb_element {
                        if msb.bit_count <= bits_to_discard {
                            self.0.buffer.pop_back();
                            bits_to_discard -= msb.bit_count;
                        } else {
                            break 'elem_discard;
                        }
                    }

                    if let Some(full) = full_elements {
                        for _ in full.indexes {
                            if u8::BIT_COUNT <= bits_to_discard {
                                self.0.buffer.pop_back();
                                bits_to_discard -= u8::BIT_COUNT;
                            } else {
                                break 'elem_discard;
                            }
                        }
                    }

                    if let Some(lsb) = lsb_element {
                        if lsb.bit_count == bits_to_discard {
                            self.0.buffer.pop_back();
                        } else {
                            break 'elem_discard;
                        }
                    }
                }
                PrimitiveElementsRegions::Single {
                    bit_offset: _,
                    bit_count,
                } => {
                    if bit_count == bits_to_discard {
                        self.0.buffer.pop_front();
                    }
                }
            }

            self.0.bit_count -= bit_count;

            value
        })
    }
}
impl<'a> BitStringEnd<'a> for BitStringMsbEnd<'a> {
    fn push<S: BitSource>(&mut self, source: S) {
        let pushed_bits_count = source.bit_count();
        let space = self.0.buffer.len() * u8::BIT_COUNT - self.0.offset.value() - self.0.len();

        if let Some(additional_elems_bit_count) = pushed_bits_count.checked_sub(space) {
            let additional_elems =
                required_primitive_elements_for_type::<u8>(0, additional_elems_bit_count);
            self.0
                .buffer
                .resize_at_back(self.0.buffer.len() + additional_elems, 0u8);
        }

        unsafe {
            source.copy_bits_to(
                self.0.buffer.as_ref().into(),
                self.0.offset.value() + self.0.bit_count,
            )
        };
        self.0.bit_count += pushed_bits_count;
    }

    #[inline]
    fn pop(&mut self) -> Option<BitValue> {
        self.pop_bits(1, get_bit_value_from_bit_str)
    }

    #[inline]
    fn pop_primitive<P: BitsPrimitive>(&mut self) -> Option<P> {
        self.pop_bits(P::BIT_COUNT, get_primitive_from_bit_str)
    }

    #[inline]
    fn pop_n(&mut self, bit_count: usize) -> Option<BitString> {
        self.pop_bits(bit_count, get_bit_string_from_bit_str)
    }

    #[inline]
    fn bit_string(&mut self) -> &mut BitString {
        self.0
    }
}

#[inline]
fn get_bit_value_from_bit_str(bit_ptr: BitPointer<u8>, _bit_count: usize) -> BitValue {
    let accessor = BitAccessor::new(bit_ptr);
    accessor.get()
}

#[inline]
fn get_primitive_from_bit_str<P: BitsPrimitive>(bit_ptr: BitPointer<u8>, _bit_count: usize) -> P {
    let mut value = P::ZERO;
    let src = bit_ptr;
    let dst = BitPointer::new_normalized(TypedPointer::from(&mut value), 0);
    unsafe { copy_bits_ptr(src, dst, P::BIT_COUNT) };
    value
}

#[inline]
fn get_bit_string_from_bit_str(bit_ptr: BitPointer<u8>, bit_count: usize) -> BitString {
    let mut buffer = LinearDeque::new();
    let offset = Offset::new(0);
    let elems_count = required_primitive_elements_typed(offset, bit_count);
    buffer.resize(elems_count, 0u8);

    let dst = BitPointer::new(TypedPointer::from(buffer.deref_mut()), offset);
    unsafe { copy_bits_ptr(bit_ptr, dst, bit_count) };

    BitString {
        buffer,
        offset,
        bit_count,
    }
}

pub struct IntoIter {
    buffer: LinearDeque<u8>,
    start_offset: usize,
    end_offset: usize,
}
impl IntoIter {
    #[inline]
    fn bit_count(&self) -> usize {
        self.end_offset - self.start_offset
    }

    #[inline]
    fn next_at_front(&mut self, bit_count: usize) -> Option<IntoIterNextItemParams> {
        (bit_count <= self.bit_count()).then(|| {
            let ptr = self.buffer.as_ref().into();
            let bit_ptr = BitPointer::new_normalized(ptr, self.start_offset);
            self.start_offset += bit_count;
            IntoIterNextItemParams { bit_ptr, bit_count }
        })
    }

    #[inline]
    fn next_at_back(&mut self, bit_count: usize) -> Option<IntoIterNextItemParams> {
        (bit_count <= self.bit_count()).then(|| {
            let ptr = self.buffer.as_ref().into();
            self.end_offset -= bit_count;
            let bit_ptr = BitPointer::new_normalized(ptr, self.end_offset);
            IntoIterNextItemParams { bit_ptr, bit_count }
        })
    }

    #[inline]
    fn get_bit_value(params: IntoIterNextItemParams) -> BitValue {
        let accessor = BitAccessor::new(params.bit_ptr);
        accessor.get()
    }

    #[inline]
    fn get_primitive<P: BitsPrimitive>(params: IntoIterNextItemParams) -> P {
        let accessor = PrimitiveAccessor::<P, _>::new(params.bit_ptr);
        accessor.get()
    }

    #[inline]
    fn get_slice(params: IntoIterNextItemParams) -> BitString {
        let buffer_elems = required_primitive_elements_for_type::<u8>(0, params.bit_count);
        let mut buffer = LinearDeque::new();
        buffer.resize(buffer_elems, 0u8);

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
impl Iterator for IntoIter {
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
impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_at_back(1).map(Self::get_bit_value)
    }
}
impl<'a> BitIterator<'a> for IntoIter {
    type PrimitiveItem<P: BitsPrimitive + 'a> = P;

    type SliceItem = BitString;

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
impl ExactSizeIterator for IntoIter {}
impl FusedIterator for IntoIter {}

struct IntoIterNextItemParams {
    bit_ptr: BitPointer<u8>,
    bit_count: usize,
}

#[cfg(test)]
mod tests {
    use std::borrow::{Borrow, BorrowMut};
    use std::ops::Deref;

    use crate::iter::BitIterator;
    use crate::BitValue::{One, Zero};
    use crate::{BitStr, BitString, BitStringEnd};

    macro_rules! bitstring {
        ($str:expr) => {
            $str.parse::<$crate::BitString>().unwrap()
        };
    }

    macro_rules! assert_bitstring {
        ($value:expr, $expected:expr) => {{
            let bit_string = &$value;
            assert_eq!(
                bit_string.buffer.len(),
                $crate::utils::required_primitive_elements_typed(
                    bit_string.offset,
                    bit_string.bit_count
                )
            );
            assert_eq!(*bit_string, $expected);
        }};
    }

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

        assert_eq!(str, [One, One, Zero, Zero, One, Zero, Zero, One]);
    }

    #[test]
    fn as_mut() {
        let mut string = BitString::from([0b10010011u8].as_ref());

        let str: &mut BitStr = string.as_mut();

        assert_eq!(str, [One, One, Zero, Zero, One, Zero, Zero, One]);
    }

    #[test]
    fn borrow() {
        let mut bit_string = bitstring!("10010011");

        let bit_str_mut: &mut BitStr = bit_string.borrow_mut();
        bit_str_mut[3].write(One);
        bit_str_mut[4].write(Zero);
        let bit_str: &BitStr = bit_string.borrow();

        assert_eq!(bit_str, BitStr::new_ref(&[0b10001011u8]));
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
            string,
            [
                One, Zero, One, One, Zero, Zero, One, Zero, Zero, One, One, Zero, Zero, Zero, One,
                One, Zero, One, One, Zero
            ]
        );
    }

    mod pop {
        use linear_deque::LinearDeque;

        use crate::refrepr::Offset;
        use crate::BitValue::{One, Zero};
        use crate::{BitString, BitStringEnd};

        #[test]
        fn lsb_pop_from_lsb_elem() {
            // ------10|101-----
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10100000u8, 0b10u8]),
                offset: Offset::new(5),
                bit_count: 5,
            };
            assert_bitstring!(bit_string, bitstring!("10101"));

            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("1010"));
            assert_eq!(bit_string.lsb().pop(), Some(Zero));
            assert_bitstring!(bit_string, bitstring!("101"));
            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("10"));
        }

        #[test]
        fn lsb_pop_from_full_elem() {
            // 10010011
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011u8]),
                offset: Offset::new(0),
                bit_count: 8,
            };
            assert_bitstring!(bit_string, bitstring!("10010011"));

            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("1001001"));
        }

        #[test]
        fn lsb_pop_from_msb_elem() {
            // -----101
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b101u8]),
                offset: Offset::new(0),
                bit_count: 3,
            };
            assert_bitstring!(bit_string, bitstring!("101"));

            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("10"));

            // -------1
            let mut bit_string = BitString {
                buffer: LinearDeque::from([1u8]),
                offset: Offset::new(0),
                bit_count: 1,
            };
            assert_bitstring!(bit_string, bitstring!("1"));

            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn lsb_pop_from_single_elem() {
            // ---101--
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10100u8]),
                offset: Offset::new(2),
                bit_count: 3,
            };
            assert_bitstring!(bit_string, bitstring!("101"));

            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("10"));
            assert_eq!(bit_string.lsb().pop(), Some(Zero));
            assert_bitstring!(bit_string, bitstring!("1"));
            assert_eq!(bit_string.lsb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn lsb_pop_empty() {
            let mut bit_string = BitString::new();

            assert_eq!(bit_string.lsb().pop(), None);
        }

        #[test]
        fn msb_pop_from_msb_elem() {
            // -----101|01------
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b01000000u8, 0b101u8]),
                offset: Offset::new(6),
                bit_count: 5,
            };
            assert_bitstring!(bit_string, bitstring!("10101"));

            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("0101"));
            assert_eq!(bit_string.msb().pop(), Some(Zero));
            assert_bitstring!(bit_string, bitstring!("101"));
            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("01"));
        }

        #[test]
        fn msb_pop_from_full_elem() {
            // 10010011
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011u8]),
                offset: Offset::new(0),
                bit_count: 8,
            };
            assert_bitstring!(bit_string, bitstring!("10010011"));

            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("0010011"));
        }

        #[test]
        fn msb_pop_from_lsb_elem() {
            // 101-----
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10100000u8]),
                offset: Offset::new(5),
                bit_count: 3,
            };
            assert_bitstring!(bit_string, bitstring!("101"));

            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("01"));

            // 1-------
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10000000u8]),
                offset: Offset::new(7),
                bit_count: 1,
            };
            assert_bitstring!(bit_string, bitstring!("1"));

            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop_from_single_elem() {
            // --101---
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b101000u8]),
                offset: Offset::new(3),
                bit_count: 3,
            };
            assert_bitstring!(bit_string, bitstring!("101"));

            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!("01"));
            assert_eq!(bit_string.msb().pop(), Some(Zero));
            assert_bitstring!(bit_string, bitstring!("1"));
            assert_eq!(bit_string.msb().pop(), Some(One));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop_empty() {
            let mut bit_string = BitString::new();

            assert_eq!(bit_string.msb().pop(), None);
        }

        #[test]
        fn all_bits() {
            let mut bit_string = bitstring!("10010011");

            assert_eq!(bit_string.lsb().pop(), Some(One)); // 1001001[1]
            assert_bitstring!(bit_string, bitstring!("1001001"));
            assert_eq!(bit_string.msb().pop(), Some(One)); // [1]001001
            assert_bitstring!(bit_string, bitstring!("001001"));
            assert_eq!(bit_string.lsb().pop(), Some(One)); // 00100[1]
            assert_bitstring!(bit_string, bitstring!("00100"));
            assert_eq!(bit_string.msb().pop(), Some(Zero)); // [0]0100
            assert_bitstring!(bit_string, bitstring!("0100"));
            assert_eq!(bit_string.lsb().pop(), Some(Zero)); // 010[0]
            assert_bitstring!(bit_string, bitstring!("010"));
            assert_eq!(bit_string.msb().pop(), Some(Zero)); // [0]10
            assert_bitstring!(bit_string, bitstring!("10"));
            assert_eq!(bit_string.lsb().pop(), Some(Zero)); // 1[0]
            assert_bitstring!(bit_string, bitstring!("1"));
            assert_eq!(bit_string.msb().pop(), Some(One)); // [1]
            assert_bitstring!(bit_string, bitstring!(""));
            assert_eq!(bit_string.lsb().pop(), None);
            assert_eq!(bit_string.msb().pop(), None);
        }
    }

    mod pop_primitive {
        use linear_deque::LinearDeque;

        use crate::refrepr::Offset;
        use crate::{BitString, BitStringEnd};

        #[test]
        fn lsb_pop_aligned() {
            // |XX|
            let mut bit_string = BitString::from(0xABu8);

            assert_eq!(bit_string.lsb().pop_primitive::<u8>(), Some(0xAB));
            assert_bitstring!(bit_string, bitstring!("0x"));

            // |XX|XX|
            let mut bit_string = BitString::from(0xABCDu16);
            assert_bitstring!(bit_string, bitstring!("0xABCD"));

            assert_eq!(bit_string.lsb().pop_primitive::<u16>(), Some(0xABCD));
            assert_bitstring!(bit_string, bitstring!("0x"));
        }

        #[test]
        fn lsb_pop_unaligned() {
            // |#X|XX|X-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xE0u8, 0xCDu8, 0xABu8]),
                offset: Offset::new(4),
                bit_count: 20,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCDE"));

            assert_eq!(bit_string.lsb().pop_primitive::<u16>(), Some(0xBCDE));
            assert_bitstring!(bit_string, bitstring!("0xA"));

            // |-X|XX|X-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xD0u8, 0xBCu8, 0xAu8]),
                offset: Offset::new(4),
                bit_count: 16,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCD"));

            assert_eq!(bit_string.lsb().pop_primitive::<u16>(), Some(0xABCD));
            assert_bitstring!(bit_string, bitstring!("0x"));
        }

        #[test]
        fn lsb_pop_none() {
            assert_eq!(bitstring!("").lsb().pop_primitive::<u8>(), None);
            assert_eq!(bitstring!("1010011").lsb().pop_primitive::<u8>(), None);
        }

        #[test]
        fn msb_pop_aligned() {
            // |XX|
            let mut bit_string = BitString::from(0xABu8);

            assert_eq!(bit_string.msb().pop_primitive::<u8>(), Some(0xAB));
            assert_bitstring!(bit_string, bitstring!("0x"));

            // |XX|XX|
            let mut bit_string = BitString::from(0xABCDu16);
            assert_bitstring!(bit_string, bitstring!("0xABCD"));

            assert_eq!(bit_string.msb().pop_primitive::<u16>(), Some(0xABCD));
            assert_bitstring!(bit_string, bitstring!("0x"));
        }

        #[test]
        fn msb_pop_unaligned() {
            // |-X|XX|X#|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xDEu8, 0xBCu8, 0xAu8]),
                offset: Offset::new(0),
                bit_count: 20,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCDE"));

            assert_eq!(bit_string.msb().pop_primitive::<u16>(), Some(0xABCD));
            assert_bitstring!(bit_string, bitstring!("0xE"));

            // |-X|XX|X-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xD0u8, 0xBCu8, 0xAu8]),
                offset: Offset::new(4),
                bit_count: 16,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCD"));

            assert_eq!(bit_string.msb().pop_primitive::<u16>(), Some(0xABCD));
            assert_bitstring!(bit_string, bitstring!("0x"));
        }

        #[test]
        fn msb_pop_none() {
            assert_eq!(bitstring!("").msb().pop_primitive::<u8>(), None);
            assert_eq!(bitstring!("1010011").msb().pop_primitive::<u8>(), None);
        }
    }

    mod pop_n {
        use linear_deque::LinearDeque;

        use crate::{refrepr::Offset, BitString, BitStringEnd};

        #[test]
        fn lsb_pop_from_lsb_elem() {
            // |##XXXX--|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b01001100]),
                offset: Offset::new(2),
                bit_count: 6,
            };
            assert_bitstring!(bit_string, bitstring!("010011"));

            assert_bitstring!(bit_string.lsb().pop_n(4).unwrap(), bitstring!("0011"));
            assert_bitstring!(bit_string, bitstring!("01"));
            assert_bitstring!(bit_string.lsb().pop_n(2).unwrap(), bitstring!("01"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn lsb_pop_from_full_elem() {
            // |XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011]),
                offset: Offset::new(0),
                bit_count: 8,
            };
            assert_bitstring!(bit_string, bitstring!("10010011"));

            assert_bitstring!(bit_string.lsb().pop_n(8).unwrap(), bitstring!("10010011"));
            assert_bitstring!(bit_string, bitstring!(""));

            // |####XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011]),
                offset: Offset::new(0),
                bit_count: 8,
            };
            assert_bitstring!(bit_string, bitstring!("10010011"));

            assert_bitstring!(bit_string.lsb().pop_n(4).unwrap(), bitstring!("0011"));
            assert_bitstring!(bit_string, bitstring!("1001"));

            // |XXXX|XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011, 0b01101100]),
                offset: Offset::new(0),
                bit_count: 16,
            };
            assert_bitstring!(bit_string, bitstring!("01101100_10010011"));

            assert_bitstring!(
                bit_string.lsb().pop_n(16).unwrap(),
                bitstring!("01101100_10010011")
            );
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn lsb_pop_from_msb_elem() {
            // |--##XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b010011]),
                offset: Offset::new(0),
                bit_count: 6,
            };
            assert_bitstring!(bit_string, bitstring!("010011"));

            assert_bitstring!(bit_string.lsb().pop_n(4).unwrap(), bitstring!("0011"));
            assert_bitstring!(bit_string, bitstring!("01"));

            // |----XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b0011]),
                offset: Offset::new(0),
                bit_count: 4,
            };
            assert_bitstring!(bit_string, bitstring!("0011"));

            assert_bitstring!(bit_string.lsb().pop_n(4).unwrap(), bitstring!("0011"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn lsb_pop_from_multiple_elems() {
            // |#X|XX|X-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xE0, 0xCD, 0xAB]),
                offset: Offset::new(4),
                bit_count: 20,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCDE"));

            assert_bitstring!(bit_string.lsb().pop_n(16).unwrap(), bitstring!("0xBCDE"));
            assert_bitstring!(bit_string, bitstring!("0xA"));

            // |-X|XX|X-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xD0, 0xBC, 0xA]),
                offset: Offset::new(4),
                bit_count: 16,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCD"));

            assert_bitstring!(bit_string.lsb().pop_n(16).unwrap(), bitstring!("0xABCD"));
            assert_bitstring!(bit_string, bitstring!("0x"));
        }

        #[test]
        fn lsb_pop_from_single_elem() {
            // |-#XXXX--|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b1011000]),
                offset: Offset::new(2),
                bit_count: 5,
            };
            assert_bitstring!(bit_string, bitstring!("10110"));

            assert_bitstring!(bit_string.lsb().pop_n(4).unwrap(), bitstring!("0110"));
            assert_bitstring!(bit_string, bitstring!("1"));

            // |--XXXX--|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b110000]),
                offset: Offset::new(2),
                bit_count: 4,
            };
            assert_bitstring!(bit_string, bitstring!("1100"));

            assert_bitstring!(bit_string.lsb().pop_n(4).unwrap(), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn lsb_pop_none() {
            assert_eq!(bitstring!("").lsb().pop_n(1), None);
            assert_eq!(bitstring!("1010011").lsb().pop_n(8), None);
        }

        #[test]
        fn msb_pop_from_msb_elem() {
            // |--XXXX##|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b010011]),
                offset: Offset::new(0),
                bit_count: 6,
            };
            assert_bitstring!(bit_string, bitstring!("010011"));

            assert_bitstring!(bit_string.msb().pop_n(4).unwrap(), bitstring!("0100"));
            assert_bitstring!(bit_string, bitstring!("11"));
            assert_bitstring!(bit_string.msb().pop_n(2).unwrap(), bitstring!("11"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop_from_full_elem() {
            // |XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011]),
                offset: Offset::new(0),
                bit_count: 8,
            };
            assert_bitstring!(bit_string, bitstring!("10010011"));

            assert_bitstring!(bit_string.msb().pop_n(8).unwrap(), bitstring!("10010011"));
            assert_bitstring!(bit_string, bitstring!(""));

            // |XXXX####|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011]),
                offset: Offset::new(0),
                bit_count: 8,
            };
            assert_bitstring!(bit_string, bitstring!("10010011"));

            assert_bitstring!(bit_string.msb().pop_n(4).unwrap(), bitstring!("1001"));
            assert_bitstring!(bit_string, bitstring!("0011"));

            // |XXXX|XXXX|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010011, 0b01101100]),
                offset: Offset::new(0),
                bit_count: 16,
            };
            assert_bitstring!(bit_string, bitstring!("01101100_10010011"));

            assert_bitstring!(
                bit_string.msb().pop_n(16).unwrap(),
                bitstring!("01101100_10010011")
            );
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop_from_lsb_elem() {
            // |XXXX##--|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b10010000]),
                offset: Offset::new(2),
                bit_count: 6,
            };
            assert_bitstring!(bit_string, bitstring!("100100"));

            assert_bitstring!(bit_string.msb().pop_n(4).unwrap(), bitstring!("1001"));
            assert_bitstring!(bit_string, bitstring!("00"));

            // |XXXX----|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b11000000]),
                offset: Offset::new(4),
                bit_count: 4,
            };
            assert_bitstring!(bit_string, bitstring!("1100"));

            assert_bitstring!(bit_string.msb().pop_n(4).unwrap(), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop_from_multiple_elems() {
            // |-X|XX|X#|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xDE, 0xBC, 0xA]),
                offset: Offset::new(0),
                bit_count: 20,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCDE"));

            assert_bitstring!(bit_string.msb().pop_n(16).unwrap(), bitstring!("0xABCD"));
            assert_bitstring!(bit_string, bitstring!("0xE"));

            // |-X|XX|X-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0xD0, 0xBC, 0xA]),
                offset: Offset::new(4),
                bit_count: 16,
            };
            assert_bitstring!(bit_string, bitstring!("0xABCD"));

            assert_bitstring!(bit_string.msb().pop_n(16).unwrap(), bitstring!("0xABCD"));
            assert_bitstring!(bit_string, bitstring!("0x"));
        }

        #[test]
        fn msb_pop_from_single_elem() {
            // |--XXXX#-|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b010010]),
                offset: Offset::new(1),
                bit_count: 5,
            };
            assert_bitstring!(bit_string, bitstring!("01001"));

            assert_bitstring!(bit_string.msb().pop_n(4).unwrap(), bitstring!("0100"));
            assert_bitstring!(bit_string, bitstring!("1"));

            // |--XXXX--|
            let mut bit_string = BitString {
                buffer: LinearDeque::from([0b110000]),
                offset: Offset::new(2),
                bit_count: 4,
            };
            assert_bitstring!(bit_string, bitstring!("1100"));

            assert_bitstring!(bit_string.msb().pop_n(4).unwrap(), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop_none() {
            assert_eq!(bitstring!("").msb().pop_n(8), None);
            assert_eq!(bitstring!("1010011").msb().pop_n(8), None);
        }
    }

    mod pop_up_to {
        use crate::BitStringEnd;

        #[test]
        fn lsb_pop() {
            let mut bit_string = bitstring!("1100");
            assert_bitstring!(bit_string.lsb().pop_up_to(3), bitstring!("100"));
            assert_bitstring!(bit_string, bitstring!("1"));

            let mut bit_string = bitstring!("1100");
            assert_bitstring!(bit_string.lsb().pop_up_to(4), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));

            let mut bit_string = bitstring!("1100");
            assert_bitstring!(bit_string.lsb().pop_up_to(5), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));
        }

        #[test]
        fn msb_pop() {
            let mut bit_string = bitstring!("1100");
            assert_bitstring!(bit_string.msb().pop_up_to(3), bitstring!("110"));
            assert_bitstring!(bit_string, bitstring!("0"));

            let mut bit_string = bitstring!("1100");
            assert_bitstring!(bit_string.msb().pop_up_to(4), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));

            let mut bit_string = bitstring!("1100");
            assert_bitstring!(bit_string.msb().pop_up_to(5), bitstring!("1100"));
            assert_bitstring!(bit_string, bitstring!(""));
        }
    }

    #[test]
    fn from_primitives_array() {
        let source: [u8; 2] = [0b10010011, 0b01101100];

        let string = BitString::from(source.as_ref());

        assert_eq!(string, BitStr::new_ref(&source));
    }

    #[test]
    fn from_bit_values_array() {
        let source = [
            One, Zero, One, One, Zero, Zero, One, One, Zero, One, One, Zero, Zero, One, One, Zero,
            One, One, Zero, Zero,
        ];

        let string: BitString = BitString::from(source.as_ref());

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
        assert_eq!(string, &source[2..14]);
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
        assert_eq!(bit_string, source);
    }

    #[test]
    fn from_iter_primitives() {
        let bits = [0b10010011u8, 0b01101100u8];

        let bit_string = BitString::from_iter(bits.into_iter());

        assert_eq!(bit_string.len(), 16);
        assert_eq!(bit_string, BitStr::new_ref(&bits));
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
            assert_eq!(bit_string.unwrap(), [Zero, Zero, One, Zero]); // 4: 0100
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
        assert_eq!(iter.next_n_back(4).unwrap(), [One, Zero, One, Zero]); // 5: 0101
        assert_eq!(iter.len(), 0); // 8765[]4FEDCB
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap(), []);
        assert_eq!(iter.next_n_back(0).unwrap(), []);
    }

    #[test]
    fn eq() {
        let mut bit_string_1 = "01".parse::<BitString>().unwrap();
        let mut bit_string_2 = "01".parse::<BitString>().unwrap();
        let mut bit_string_ne = "10".parse::<BitString>().unwrap();

        assert!(bit_string_1 == bit_string_1);
        assert!(bit_string_1 == bit_string_2);
        assert!(bit_string_1 != bit_string_ne);

        assert!(bit_string_1 == bit_string_1.as_bit_str());
        assert!(bit_string_1 == bit_string_2.as_bit_str());
        assert!(bit_string_1 != bit_string_ne.as_bit_str());

        assert!(bit_string_1 == bit_string_1.clone().as_bit_str_mut());
        assert!(bit_string_1 == bit_string_2.as_bit_str_mut());
        assert!(bit_string_1 != bit_string_ne.as_bit_str_mut());

        assert!(bit_string_1.as_bit_str() == bit_string_1);
        assert!(bit_string_1.as_bit_str() == bit_string_2);
        assert!(bit_string_1.as_bit_str() != bit_string_ne);

        assert!(bit_string_1.clone().as_bit_str_mut() == bit_string_1);
        assert!(bit_string_1.as_bit_str_mut() == bit_string_2);
        assert!(bit_string_1.as_bit_str_mut() != bit_string_ne);

        assert!(bit_string_1 == [One, Zero]);
        assert!(bit_string_1 != [Zero, One]);

        assert!([One, Zero] == bit_string_1);
        assert!([Zero, One] != bit_string_1);

        assert!(vec![One, Zero] == bit_string_1);
        assert!(vec![Zero, One] != bit_string_1);
    }

    #[test]
    fn ord() {
        let bit_string = bitstring!("0xBB00BB");
        let empty = BitString::new();
        let zero = bitstring!("0");
        let one = bitstring!("1");

        assert!(!(bit_string < bit_string));
        assert!(!(bit_string < bitstring!("0xBB00BB")));
        assert!(bit_string < bitstring!("0xBB00CC")); // MSByte is equal but LSByte is larger
        assert!(bit_string < bitstring!("0xCC00AA")); // MSByte is larger but LSByte is smaller
        assert!(empty < zero); // "" < "0"
        assert!(zero > empty); // "0" > ""
        assert!(zero < one); // "0" < "1"

        assert!(!(bit_string < bit_string.as_bit_str()));
        assert!(!(bit_string < bit_string.clone().as_bit_str_mut()));
        assert!(!(bit_string.as_bit_str() < bit_string));
        assert!(!(bit_string.clone().as_bit_str_mut() < bit_string));
    }

    #[test]
    fn from_str() {
        macro_rules! assert_ok {
            ($str:literal, $expected_bits:expr) => {
                let parsed = $str.parse::<BitString>().unwrap();
                assert_eq!(parsed, $expected_bits);
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
                assert_eq!(parsed.unwrap(), $bit_string);
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
