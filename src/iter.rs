use std::iter::FusedIterator;
use std::marker::PhantomData;

use crate::ref_encoding::bit_pointer::BitPointer;
use crate::ref_encoding::byte_pointer::BytePointer;
use crate::ref_encoding::{RefComponents, RefRepr};
use crate::{Bit, BitAccessor, BitValue, PrimitiveAccessor};
use crate::{BitStr, BitsPrimitive, Primitive};

pub trait BitIterator<'a>:
    Iterator + DoubleEndedIterator + ExactSizeIterator + FusedIterator + Sized
{
    type PrimitiveItem<P: BitsPrimitive + 'a>;
    type SliceItem;

    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>>;
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>>;
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem>;
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem>;

    #[inline]
    fn reverse(self) -> ReverseIter<'a, Self> {
        ReverseIter {
            inner: self,
            phantom: PhantomData,
        }
    }

    #[inline]
    fn primitives<P: BitsPrimitive>(self) -> PrimitivesIter<'a, P, Self> {
        PrimitivesIter {
            inner: self,
            phantom: PhantomData,
        }
    }

    #[inline]
    fn subslices(self, len: usize) -> SubslicesIter<'a, Self> {
        SubslicesIter {
            inner: self,
            slice_len: len,
            phantom: PhantomData,
        }
    }
}

pub(crate) struct RawIter<'a> {
    byte_ptr: BytePointer,
    start_offset: usize,
    end_offset: usize,
    phantom: PhantomData<&'a ()>,
}
impl<'a> From<RefComponents> for RawIter<'a> {
    #[inline]
    fn from(components: RefComponents) -> Self {
        let byte_ptr = components.bit_ptr.byte_ptr();
        let start_offset = components.bit_ptr.offset().value();
        let end_offset = start_offset + components.bit_count;
        RawIter {
            byte_ptr,
            start_offset,
            end_offset,
            phantom: PhantomData,
        }
    }
}
impl<'a> RawIter<'a> {
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn next_at_front<F, R>(&mut self, bit_count: usize, f: F) -> Option<R>
    where
        F: FnOnce(NextOutputArgs) -> R,
    {
        (bit_count <= self.len()).then(|| {
            let args = NextOutputArgs {
                byte_ptr: self.byte_ptr,
                offset: self.start_offset,
                bit_count,
            };
            let value = f(args);
            self.start_offset += bit_count;
            value
        })
    }

    #[inline]
    fn next_at_back<F, R>(&mut self, bit_count: usize, f: F) -> Option<R>
    where
        F: FnOnce(NextOutputArgs) -> R,
    {
        (bit_count <= self.len()).then(|| {
            self.end_offset -= bit_count;
            let args = NextOutputArgs {
                byte_ptr: self.byte_ptr,
                offset: self.end_offset,
                bit_count,
            };
            f(args)
        })
    }

    #[inline]
    fn len(&self) -> usize {
        self.end_offset - self.start_offset
    }
}

struct NextOutputArgs {
    byte_ptr: BytePointer,
    offset: usize,
    bit_count: usize,
}

pub struct Iter<'a>(pub(crate) RawIter<'a>);
impl<'a> Iterator for Iter<'a> {
    type Item = BitValue;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next_at_front(1, next_bit_value)
    }
}
impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_at_back(1, next_bit_value)
    }
}
impl<'a> BitIterator<'a> for Iter<'a> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = P;
    type SliceItem = &'a BitStr;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0.next_at_front(P::BIT_COUNT, next_primitive::<P>)
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0.next_at_back(P::BIT_COUNT, next_primitive::<P>)
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_front(len, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_back(len, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> ExactSizeIterator for Iter<'a> {}
impl<'a> FusedIterator for Iter<'a> {}

pub struct IterRef<'a>(pub(crate) RawIter<'a>);
impl<'a> Iterator for IterRef<'a> {
    type Item = &'a Bit;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next_at_front(1, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> DoubleEndedIterator for IterRef<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_at_back(1, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> BitIterator<'a> for IterRef<'a> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = &'a Primitive<P>;
    type SliceItem = &'a BitStr;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_front(P::BIT_COUNT, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_back(P::BIT_COUNT, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_front(len, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_back(len, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> ExactSizeIterator for IterRef<'a> {}
impl<'a> FusedIterator for IterRef<'a> {}

pub struct IterMut<'a>(pub(crate) RawIter<'a>);
impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Bit;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next_at_front(1, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> DoubleEndedIterator for IterMut<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_at_back(1, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> BitIterator<'a> for IterMut<'a> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = &'a mut Primitive<P>;
    type SliceItem = &'a mut BitStr;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_front(P::BIT_COUNT, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_back(P::BIT_COUNT, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_front(len, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_back(len, next_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> ExactSizeIterator for IterMut<'a> {}
impl<'a> FusedIterator for IterMut<'a> {}

#[inline]
fn next_bit_value(args: NextOutputArgs) -> BitValue {
    let bit_ptr = BitPointer::new_normalized(args.byte_ptr, args.offset);
    let accessor = BitAccessor::new(bit_ptr);
    accessor.get()
}

#[inline]
fn next_primitive<P: BitsPrimitive>(args: NextOutputArgs) -> P {
    let bit_ptr = BitPointer::new_normalized(args.byte_ptr, args.offset);
    let accessor = PrimitiveAccessor::new(bit_ptr);
    accessor.get()
}

#[inline]
fn next_ref_repr(args: NextOutputArgs) -> RefRepr {
    let components = RefComponents {
        bit_ptr: BitPointer::new_normalized(args.byte_ptr, args.offset),
        bit_count: args.bit_count,
    };
    components.encode()
}

pub struct ReverseIter<'a, I: BitIterator<'a>> {
    inner: I,
    phantom: PhantomData<&'a ()>,
}
impl<'a, I: BitIterator<'a>> Iterator for ReverseIter<'a, I> {
    type Item = I::Item;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}
impl<'a, I: BitIterator<'a>> DoubleEndedIterator for ReverseIter<'a, I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}
impl<'a, I: BitIterator<'a>> BitIterator<'a> for ReverseIter<'a, I> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = I::PrimitiveItem<P>;
    type SliceItem = I::SliceItem;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.inner.next_primitive_back::<P>()
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.inner.next_primitive::<P>()
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.inner.next_n_back(len)
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.inner.next_n(len)
    }
}
impl<'a, I: BitIterator<'a>> ExactSizeIterator for ReverseIter<'a, I> {}
impl<'a, I: BitIterator<'a>> FusedIterator for ReverseIter<'a, I> {}

trait BitBlockIterator: Iterator + DoubleEndedIterator + ExactSizeIterator + FusedIterator {
    type Remainder;

    fn into_remainder(self) -> Option<Self::Remainder>;
    fn block_len(&self) -> usize;
    fn remainder_bit_count(&self) -> usize;
}

pub struct PrimitivesIter<'a, P: BitsPrimitive, I: BitIterator<'a>> {
    inner: I,
    phantom: PhantomData<&'a P>,
}
impl<'a, P: BitsPrimitive, I: BitIterator<'a>> BitBlockIterator for PrimitivesIter<'a, P, I> {
    type Remainder = I::SliceItem;

    #[inline]
    fn into_remainder(mut self) -> Option<Self::Remainder> {
        for _ in self.by_ref() {}

        let remainder_bit_count = self.remainder_bit_count();
        if remainder_bit_count > 0 {
            self.inner.next_n(remainder_bit_count)
        } else {
            None
        }
    }

    #[inline]
    fn block_len(&self) -> usize {
        P::BIT_COUNT
    }

    #[inline]
    fn remainder_bit_count(&self) -> usize {
        self.inner.len() % self.block_len()
    }
}
impl<'a, P: BitsPrimitive, I: BitIterator<'a>> Iterator for PrimitivesIter<'a, P, I> {
    type Item = I::PrimitiveItem<P>;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.len() / self.block_len();
        (len, Some(len))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_primitive::<P>()
    }
}
impl<'a, P: BitsPrimitive, I: BitIterator<'a>> DoubleEndedIterator for PrimitivesIter<'a, P, I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_primitive_back::<P>()
    }
}
impl<'a, P: BitsPrimitive, I: BitIterator<'a>> ExactSizeIterator for PrimitivesIter<'a, P, I> {}
impl<'a, P: BitsPrimitive, I: BitIterator<'a>> FusedIterator for PrimitivesIter<'a, P, I> {}

pub struct SubslicesIter<'a, I: BitIterator<'a>> {
    inner: I,
    slice_len: usize,
    phantom: PhantomData<&'a ()>,
}
impl<'a, I: BitIterator<'a>> BitBlockIterator for SubslicesIter<'a, I> {
    type Remainder = I::SliceItem;

    #[inline]
    fn into_remainder(mut self) -> Option<Self::Remainder> {
        for _ in self.by_ref() {}

        let remainder_bit_count = self.remainder_bit_count();
        if remainder_bit_count > 0 {
            self.inner.next_n(remainder_bit_count)
        } else {
            None
        }
    }

    #[inline]
    fn block_len(&self) -> usize {
        self.slice_len
    }

    #[inline]
    fn remainder_bit_count(&self) -> usize {
        self.inner.len() % self.block_len()
    }
}
impl<'a, I: BitIterator<'a>> Iterator for SubslicesIter<'a, I> {
    type Item = I::SliceItem;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.len() / self.block_len();
        (len, Some(len))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_n(self.slice_len)
    }
}
impl<'a, I: BitIterator<'a>> DoubleEndedIterator for SubslicesIter<'a, I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_n_back(self.slice_len)
    }
}
impl<'a, I: BitIterator<'a>> ExactSizeIterator for SubslicesIter<'a, I> {}
impl<'a, I: BitIterator<'a>> FusedIterator for SubslicesIter<'a, I> {}

#[cfg(test)]
mod tests {
    use crate::iter::{BitBlockIterator, BitIterator};
    use crate::BitStr;
    use crate::BitValue::{One, Zero};

    #[test]
    fn iter() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x76]; // In memory: 76FEDCBA
        let bit_str = BitStr::new_ref(&memory);

        let mut iter = bit_str.iter();

        assert_eq!(iter.len(), 32); // [76FEDCBA]
        assert_eq!(iter.next(), Some(Zero)); // A: 101[0]
        assert_eq!(iter.next(), Some(One)); // A: 10[1]0
        assert_eq!(iter.next(), Some(Zero)); // A: 1[0]10
        assert_eq!(iter.next(), Some(One)); // A: [1]010
        assert_eq!(iter.len(), 28); // [76FEDCB]A
        assert_eq!(iter.next_primitive::<u8>(), Some(0xCB));
        assert_eq!(iter.len(), 20); // [76FED]CBA
        assert_eq!(iter.next_n(4).unwrap(), [One, Zero, One, One]); // D: 1101
        assert_eq!(iter.len(), 16); // [76FE]DCBA
        assert_eq!(iter.next(), Some(Zero)); // E: 111[0]
        assert_eq!(iter.next(), Some(One)); // E: 11[1]0
        assert_eq!(iter.next(), Some(One)); // E: 1[1]10
        assert_eq!(iter.next(), Some(One)); // E: [1]110
        assert_eq!(iter.len(), 12); // [76F]EDCBA
        assert_eq!(iter.next_primitive::<u8>(), Some(0x6F));
        assert_eq!(iter.len(), 4); // [7]6FEDCBA
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert_eq!(iter.next_n(4).unwrap(), [One, One, One, Zero]); // 7: 0111
        assert_eq!(iter.len(), 0); // []76FEDCBA
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert_eq!(iter.next_n(0).unwrap(), []);
    }

    #[test]
    fn iter_double_ended() {
        let memory: [u8; 6] = [0xBA, 0xDC, 0xFE, 0x54, 0x76, 0x98]; // In memory: 987654FEDCBA
        let bit_str = BitStr::new_ref(&memory);

        let mut iter = bit_str[4..44].iter(); // 87654FEDCB

        assert_eq!(iter.len(), 40); // [87654FEDCB]
        assert_eq!(iter.next(), Some(One)); // B: 101[1]
        assert_eq!(iter.next(), Some(One)); // B: 10[1]1
        assert_eq!(iter.next(), Some(Zero)); // B: 1[0]11
        assert_eq!(iter.next(), Some(One)); // B: [1]011
        assert_eq!(iter.len(), 36); // [87654FEDC]B
        assert_eq!(iter.next_primitive::<u16>(), Some(0xFEDC));
        assert_eq!(iter.len(), 20); // [87654]FEDCB
        assert_eq!(iter.next_n(4).unwrap(), [Zero, Zero, One, Zero]); // 4: 0100
        assert_eq!(iter.len(), 16); // [8765]4FEDCB
        assert_eq!(iter.next_back(), Some(One)); // 8: [1]000
        assert_eq!(iter.next_back(), Some(Zero)); // 8: 1[0]00
        assert_eq!(iter.next_back(), Some(Zero)); // 8: 10[0]0
        assert_eq!(iter.next_back(), Some(Zero)); // 8: 100[0]
        assert_eq!(iter.len(), 12); // 8[765]4FEDCB
        assert_eq!(iter.next_primitive_back::<u8>(), Some(0x76));
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
    fn iter_ref() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x76]; // In memory: 76FEDCBA
        let bit_str = BitStr::new_ref(&memory);

        let mut iter = bit_str.iter_ref();

        assert_eq!(iter.len(), 32); // [76FEDCBA]
        assert_eq!(iter.next().unwrap(), Zero); // A: 101[0]
        assert_eq!(iter.next().unwrap(), One); // A: 10[1]0
        assert_eq!(iter.next().unwrap(), Zero); // A: 1[0]10
        assert_eq!(iter.next().unwrap(), One); // A: [1]010
        assert_eq!(iter.len(), 28); // [76FEDCB]A
        assert_eq!(iter.next_primitive::<u8>().unwrap().read(), 0xCB);
        assert_eq!(iter.len(), 20); // [76FED]CBA
        assert_eq!(iter.next_n(4).unwrap(), [One, Zero, One, One]); // D: 1101
        assert_eq!(iter.len(), 16); // [76FE]DCBA
        assert_eq!(iter.next().unwrap(), Zero); // E: 111[0]
        assert_eq!(iter.next().unwrap(), One); // E: 11[1]0
        assert_eq!(iter.next().unwrap(), One); // E: 1[1]10
        assert_eq!(iter.next().unwrap(), One); // E: [1]110
        assert_eq!(iter.len(), 12); // [76F]EDCBA
        assert_eq!(iter.next_primitive::<u8>().unwrap().read(), 0x6F);
        assert_eq!(iter.len(), 4); // [7]6FEDCBA
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert_eq!(iter.next_n(4).unwrap(), [One, One, One, Zero]); // 7: 0111
        assert_eq!(iter.len(), 0); // []76FEDCBA
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert_eq!(iter.next_n(0).unwrap(), []);
    }

    #[test]
    fn iter_ref_double_ended() {
        let memory: [u8; 6] = [0xBA, 0xDC, 0xFE, 0x54, 0x76, 0x98]; // In memory: 987654FEDCBA
        let bit_str = BitStr::new_ref(&memory);

        let mut iter = bit_str[4..44].iter_ref(); // 87654FEDCB

        assert_eq!(iter.len(), 40); // [87654FEDCB]
        assert_eq!(iter.next().unwrap(), One); // B: 101[1]
        assert_eq!(iter.next().unwrap(), One); // B: 10[1]1
        assert_eq!(iter.next().unwrap(), Zero); // B: 1[0]11
        assert_eq!(iter.next().unwrap(), One); // B: [1]011
        assert_eq!(iter.len(), 36); // [87654FEDC]B
        assert_eq!(iter.next_primitive::<u16>().unwrap().read(), 0xFEDC);
        assert_eq!(iter.len(), 20); // [87654]FEDCB
        assert_eq!(iter.next_n(4).unwrap(), [Zero, Zero, One, Zero]); // 4: 0100
        assert_eq!(iter.len(), 16); // [8765]4FEDCB
        assert_eq!(iter.next_back().unwrap(), One); // 8: [1]000
        assert_eq!(iter.next_back().unwrap(), Zero); // 8: 1[0]00
        assert_eq!(iter.next_back().unwrap(), Zero); // 8: 10[0]0
        assert_eq!(iter.next_back().unwrap(), Zero); // 8: 100[0]
        assert_eq!(iter.len(), 12); // 8[765]4FEDCB
        assert_eq!(iter.next_primitive_back::<u8>().unwrap().read(), 0x76);
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
    fn iter_mut() {
        let mut memory: [u8; 6] = [0xBA, 0xDC, 0xFE, 0x54, 0x76, 0x98]; // In memory: 987654FEDCBA
        let bit_str = BitStr::new_mut(&mut memory);

        let mut iter = bit_str[4..44].iter_mut(); // 87654FEDCB

        assert_eq!(iter.len(), 40); // [87654FEDCB]
        assert_eq!(iter.next().unwrap().read(), One); // B: 101[1]
        assert_eq!(iter.next().unwrap().read(), One); // B: 10[1]1
        assert_eq!(iter.next().unwrap().write(One), Zero); // B: 1[0]11 -> F: 1[1]11
        assert_eq!(iter.next().unwrap().read(), One); // F: [1]111
        assert_eq!(iter.len(), 36); // [87654FEDC]F
        iter.next_primitive::<u16>().unwrap().modify(|value| {
            assert_eq!(value, 0xFEDC);
            !value
        }); // [87654]0123]F
        assert_eq!(iter.len(), 20); // [87654]0123F
        assert_eq!(iter.next_n(4).unwrap(), [Zero, Zero, One, Zero]); // 4: 0100
        assert_eq!(iter.len(), 16); // [8765]40123F
        assert_eq!(iter.next_back().unwrap().read(), One); // 8: [1]000
        assert_eq!(iter.next_back().unwrap().read(), Zero); // 8: 1[0]00
        assert_eq!(iter.next_back().unwrap().read(), Zero); // 8: 10[0]0
        assert_eq!(iter.next_back().unwrap().read(), Zero); // 8: 100[0]
        assert_eq!(iter.len(), 12); // 8[765]40123F
        assert_eq!(iter.next_primitive_back::<u8>().unwrap().read(), 0x76);
        assert_eq!(iter.len(), 4); // 876[5]40123F
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert!(iter.next_n_back(5).is_none());
        assert_eq!(iter.next_n_back(4).unwrap(), [One, Zero, One, Zero]); // 5: 0101
        assert_eq!(iter.len(), 0); // 8765[]40123F
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap(), []);
        assert_eq!(iter.next_n_back(0).unwrap(), []);
        assert_eq!(memory, [0xFA, 0x23, 0x01, 0x54, 0x76, 0x98]); // In memory: 9876540123FA
    }

    #[test]
    fn into_iter() {
        let memory = [0b10010011u8];
        let bit_str = &BitStr::new_ref(&memory)[1..7];

        let mut iter = bit_str.into_iter();

        assert_eq!(iter.next().unwrap(), One);
        assert_eq!(iter.next().unwrap(), Zero);
        assert_eq!(iter.next().unwrap(), Zero);
        assert_eq!(iter.next().unwrap(), One);
        assert_eq!(iter.next().unwrap(), Zero);
        assert_eq!(iter.next().unwrap(), Zero);
        assert!(iter.next().is_none());
    }

    #[test]
    fn primitives() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x32]; // In memory: 32FEDCBA
        let bit_str = &BitStr::new_ref(&memory)[8..28]; // 3[2FEDC]BA

        let mut iter = bit_str.iter().primitives::<u8>();

        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next(), Some(0xDC)); // 3[2FE]DCBA
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next_back(), Some(0x2F)); // 32F[E]DCBA
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
        assert_eq!(iter.into_remainder().unwrap(), [Zero, One, One, One]); // E: 1110
    }

    #[test]
    fn primitives_mut_no_remainder() {
        let mut memory: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: FEDCBA
        let bit_str = &mut BitStr::new_mut(&mut memory)[4..20]; // F[EDCB]A

        let mut iter = bit_str.iter_mut().primitives::<u8>();

        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next_back().unwrap().write(0x54), 0xED); // F[EDCB]A -> F54[CB]A
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next().unwrap().write(0x32), 0xCB); // F54[CB]A -> F54[]32A
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.into_remainder().is_none());
        assert_eq!(memory, [0x2A, 0x43, 0xF5]); // In memory: F5432A
    }

    #[test]
    fn subslices() {
        let memory: [u8; 4] = [0xBA, 0xDC, 0xFE, 0x32]; // In memory: 32FEDCBA
        let bit_str = &BitStr::new_ref(&memory)[8..28]; // 3[2FEDC]BA

        let mut iter = bit_str.iter().subslices(8);

        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next().unwrap().get_primitive::<u8>(0).unwrap(), 0xDC); // 3[2FE]DCBA
        assert_eq!(iter.len(), 1);
        assert_eq!(
            iter.next_back().unwrap().get_primitive::<u8>(0).unwrap(),
            0x2F
        ); // 32F[E]DCBA
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
        assert_eq!(iter.into_remainder().unwrap(), [Zero, One, One, One]); // E: 1110
    }

    #[test]
    fn subslices_mut_no_remainder() {
        let mut memory: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: FEDCBA
        let bit_str = &mut BitStr::new_mut(&mut memory)[4..20]; // F[EDCB]A

        let mut iter = bit_str.iter_mut().subslices(8);

        assert_eq!(iter.len(), 2);
        assert_eq!(
            iter.next_back()
                .unwrap()
                .get_primitive_mut::<u8>(0)
                .unwrap()
                .write(0x54),
            0xED
        ); // F[EDCB]A -> F54[CB]A
        assert_eq!(iter.len(), 1);
        assert_eq!(
            iter.next()
                .unwrap()
                .get_primitive_mut::<u8>(0)
                .unwrap()
                .write(0x32),
            0xCB
        ); // F54[CB]A -> F54[]32A
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.into_remainder().is_none());
        assert_eq!(memory, [0x2A, 0x43, 0xF5]); // In memory: F5432A
    }

    #[test]
    fn reverse() {
        let memory: [u8; 6] = [0xBA, 0xDC, 0xFE, 0x54, 0x76, 0x98]; // In memory: 987654FEDCBA
        let bit_str = BitStr::new_ref(&memory);

        let mut iter = bit_str[4..44].iter().reverse(); // [87654FEDCB]

        assert_eq!(iter.len(), 40); // [87654FEDCB]
        assert_eq!(iter.next(), Some(One)); // 8: [1]000
        assert_eq!(iter.next(), Some(Zero)); // 8: 1[0]00
        assert_eq!(iter.next(), Some(Zero)); // 8: 10[0]0
        assert_eq!(iter.next(), Some(Zero)); // 8: 100[0]
        assert_eq!(iter.len(), 36); // 8[7654FEDCB]
        assert_eq!(iter.next_primitive::<u16>(), Some(0x7654));
        assert_eq!(iter.len(), 20); // 87654[FEDCB]
        assert_eq!(iter.next_n(4).unwrap(), [One, One, One, One]); // F: 1111
        assert_eq!(iter.len(), 16); // 87654F[EDCB]
        assert_eq!(iter.next_back(), Some(One)); // B: 101[1]
        assert_eq!(iter.next_back(), Some(One)); // B: 10[1]1
        assert_eq!(iter.next_back(), Some(Zero)); // B: 1[0]11
        assert_eq!(iter.next_back(), Some(One)); // B: [1]011
        assert_eq!(iter.len(), 12); // 87654F[EDC]B
        assert_eq!(iter.next_primitive_back::<u8>(), Some(0xDC));
        assert_eq!(iter.len(), 4); // 87654F[E]DCB
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert!(iter.next_n_back(5).is_none());
        assert_eq!(iter.next_n_back(4).unwrap(), [Zero, One, One, One]); // E: 1110
        assert_eq!(iter.len(), 0); // 87654F[]EDCB
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap(), []);
        assert_eq!(iter.next_n_back(0).unwrap(), []);
    }
}
