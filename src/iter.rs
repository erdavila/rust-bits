use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::refrepr::{RefRepr, TypedRefComponents, UntypedRefComponents};
use crate::utils::normalize_ptr_and_offset;
use crate::{Bit, BitAccessor, BitValue, BitsPrimitiveDiscriminant, BitsPrimitiveSelector};
use crate::{BitStr, BitsPrimitive, Primitive, PrimitiveAccessor};

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
    fn primitives<P: BitsPrimitive>(self) -> PrimitivesIter<'a, P, Self> {
        PrimitivesIter {
            inner: self,
            phantom: PhantomData,
        }
    }
}

pub(crate) struct RawIter<'a> {
    ptr: NonNull<()>,
    underlying_primitive: BitsPrimitiveDiscriminant,
    start_offset: usize,
    end_offset: usize,
    phantom: PhantomData<&'a ()>,
}
impl<'a> From<UntypedRefComponents> for RawIter<'a> {
    #[inline]
    fn from(components: UntypedRefComponents) -> Self {
        let metadata = components.metadata;
        RawIter {
            ptr: components.ptr,
            underlying_primitive: metadata.underlying_primitive,
            start_offset: metadata.offset,
            end_offset: metadata.offset + metadata.bit_count,
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
        F: FnOnce(SelectOutputArgs) -> R,
    {
        (bit_count <= self.len()).then(|| {
            let args = SelectOutputArgs {
                ptr: self.ptr,
                underlying_primitive: self.underlying_primitive,
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
        F: FnOnce(SelectOutputArgs) -> R,
    {
        (bit_count <= self.len()).then(|| {
            self.end_offset -= bit_count;
            let args = SelectOutputArgs {
                ptr: self.ptr,
                underlying_primitive: self.underlying_primitive,
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

struct SelectOutputArgs {
    ptr: NonNull<()>,
    underlying_primitive: BitsPrimitiveDiscriminant,
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
        self.0.next_at_front(1, select_bit_value)
    }
}
impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_at_back(1, select_bit_value)
    }
}
impl<'a> BitIterator<'a> for Iter<'a> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = P;
    type SliceItem = &'a BitStr;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0.next_at_front(P::BIT_COUNT, select_primitive::<P>)
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0.next_at_back(P::BIT_COUNT, select_primitive::<P>)
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_front(len, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_back(len, select_ref_repr)
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
            .next_at_front(1, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> DoubleEndedIterator for IterRef<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_at_back(1, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> BitIterator<'a> for IterRef<'a> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = &'a Primitive<P>;
    type SliceItem = &'a BitStr;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_front(P::BIT_COUNT, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_back(P::BIT_COUNT, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_front(len, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_back(len, select_ref_repr)
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
            .next_at_front(1, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> DoubleEndedIterator for IterMut<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_at_back(1, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> BitIterator<'a> for IterMut<'a> {
    type PrimitiveItem<P: BitsPrimitive + 'a> = &'a mut Primitive<P>;
    type SliceItem = &'a mut BitStr;

    #[inline]
    fn next_primitive<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_front(P::BIT_COUNT, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_primitive_back<P: BitsPrimitive + 'a>(&mut self) -> Option<Self::PrimitiveItem<P>> {
        self.0
            .next_at_back(P::BIT_COUNT, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_front(len, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_n_back(&mut self, len: usize) -> Option<Self::SliceItem> {
        self.0
            .next_at_back(len, select_ref_repr)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}
impl<'a> ExactSizeIterator for IterMut<'a> {}
impl<'a> FusedIterator for IterMut<'a> {}

#[inline]
fn select_bit_value(args: SelectOutputArgs) -> BitValue {
    args.underlying_primitive.select({
        struct Selector {
            ptr: NonNull<()>,
            offset: usize,
        }
        impl BitsPrimitiveSelector for Selector {
            type Output = BitValue;
            #[inline]
            fn select<U: crate::BitsPrimitive>(self) -> Self::Output {
                let (ptr, offset) =
                    unsafe { normalize_ptr_and_offset(self.ptr.cast::<U>(), self.offset) };
                let accessor = BitAccessor::new(ptr, offset);
                accessor.get()
            }
        }
        Selector {
            ptr: args.ptr,
            offset: args.offset,
        }
    })
}

#[inline]
fn select_primitive<P: BitsPrimitive>(args: SelectOutputArgs) -> P {
    args.underlying_primitive.select({
        struct Selector<P> {
            ptr: NonNull<()>,
            offset: usize,
            phantom: PhantomData<P>,
        }
        impl<P: BitsPrimitive> BitsPrimitiveSelector for Selector<P> {
            type Output = P;
            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                let accessor = PrimitiveAccessor::<P, U>::new(self.ptr.cast(), self.offset);
                accessor.get()
            }
        }
        Selector::<P> {
            ptr: args.ptr,
            offset: args.offset,
            phantom: PhantomData,
        }
    })
}

#[inline]
fn select_ref_repr(args: SelectOutputArgs) -> RefRepr {
    args.underlying_primitive.select({
        struct Selector {
            ptr: NonNull<()>,
            offset: usize,
            bit_count: usize,
        }
        impl BitsPrimitiveSelector for Selector {
            type Output = RefRepr;
            #[inline]
            fn select<U: BitsPrimitive>(self) -> Self::Output {
                let components = TypedRefComponents::new_normalized(
                    self.ptr.cast::<U>(),
                    self.offset,
                    self.bit_count,
                );
                components.encode()
            }
        }
        Selector {
            ptr: args.ptr,
            offset: args.offset,
            bit_count: args.bit_count,
        }
    })
}

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

#[cfg(test)]
mod tests {
    use crate::iter::{BitBlockIterator, BitIterator};
    use crate::BitStr;
    use crate::BitValue::{One, Zero};

    #[test]
    fn iter() {
        let memory: [u16; 2] = [0xDCBA, 0x76FE]; // In memory: 76FEDCBA
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
        assert_eq!(iter.next_n(4).unwrap(), &[One, Zero, One, One]); // D: 1101
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
        assert_eq!(iter.next_n(4).unwrap(), &[One, One, One, Zero]); // 7: 0111
        assert_eq!(iter.len(), 0); // []76FEDCBA
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert_eq!(iter.next_n(0).unwrap(), &[]);
    }

    #[test]
    fn iter_double_ended() {
        let memory: [u16; 3] = [0xDCBA, 0x54FE, 0x9876]; // In memory: 987654FEDCBA
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
        assert_eq!(iter.next_n(4).unwrap(), &[Zero, Zero, One, Zero]); // 4: 0100
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
        assert_eq!(iter.next_n_back(4).unwrap(), &[One, Zero, One, Zero]); // 5: 0101
        assert_eq!(iter.len(), 0); // 8765[]4FEDCB
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap(), &[]);
        assert_eq!(iter.next_n_back(0).unwrap(), &[]);
    }

    #[test]
    fn iter_ref() {
        let memory: [u16; 2] = [0xDCBA, 0x76FE]; // In memory: 76FEDCBA
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
        assert_eq!(iter.next_n(4).unwrap(), &[One, Zero, One, One]); // D: 1101
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
        assert_eq!(iter.next_n(4).unwrap(), &[One, One, One, Zero]); // 7: 0111
        assert_eq!(iter.len(), 0); // []76FEDCBA
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(5).is_none());
        assert_eq!(iter.next_n(0).unwrap(), &[]);
    }

    #[test]
    fn iter_ref_double_ended() {
        let memory: [u16; 3] = [0xDCBA, 0x54FE, 0x9876]; // In memory: 987654FEDCBA
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
        assert_eq!(iter.next_n(4).unwrap(), &[Zero, Zero, One, Zero]); // 4: 0100
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
        assert_eq!(iter.next_n_back(4).unwrap(), &[One, Zero, One, Zero]); // 5: 0101
        assert_eq!(iter.len(), 0); // 8765[]4FEDCB
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap(), &[]);
        assert_eq!(iter.next_n_back(0).unwrap(), &[]);
    }

    #[test]
    fn iter_mut() {
        let mut memory: [u16; 3] = [0xDCBA, 0x54FE, 0x9876]; // In memory: 987654FEDCBA
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
        assert_eq!(iter.next_n(4).unwrap(), &[Zero, Zero, One, Zero]); // 4: 0100
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
        assert_eq!(iter.next_n_back(4).unwrap(), &[One, Zero, One, Zero]); // 5: 0101
        assert_eq!(iter.len(), 0); // 8765[]40123F
        assert!(iter.next().is_none());
        assert!(iter.next_primitive::<u8>().is_none());
        assert!(iter.next_n(1).is_none());
        assert!(iter.next_back().is_none());
        assert!(iter.next_primitive_back::<u8>().is_none());
        assert!(iter.next_n_back(1).is_none());
        assert_eq!(iter.next_n(0).unwrap(), &[]);
        assert_eq!(iter.next_n_back(0).unwrap(), &[]);
        assert_eq!(memory, [0x23FA, 0x5401, 0x9876]); // In memory: 9876540123FA
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
        let memory: [u16; 2] = [0xDCBA, 0x32FE]; // In memory: 32FEDCBA
        let bit_str = &BitStr::new_ref(&memory)[8..28]; // 3[2FEDC]BA

        let mut iter = bit_str.iter().primitives::<u8>();

        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next(), Some(0xDC)); // 3[2FE]DCBA
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next_back(), Some(0x2F)); // 32F[E]DCBA
        assert_eq!(iter.len(), 0);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
        assert_eq!(iter.into_remainder().unwrap(), &[Zero, One, One, One]); // E: 1110
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
}
