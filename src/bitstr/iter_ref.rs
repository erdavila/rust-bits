use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::refrepr::{RefRepr, TypedRefComponents};
use crate::{
    Bit, BitStr, BitsPrimitive, BitsPrimitiveDiscriminant, BitsPrimitiveSelector, Primitive,
};

pub struct IterRef<'a> {
    pub(crate) ptr: NonNull<()>,
    pub(crate) underlying_primitive: BitsPrimitiveDiscriminant,
    pub(crate) start_offset: usize,
    pub(crate) end_offset: usize,
    pub(crate) phantom: PhantomData<&'a ()>,
}

impl<'a> Iterator for IterRef<'a> {
    type Item = &'a Bit;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end_offset - self.start_offset;
        (size, Some(size))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.next_at_front(1, IterBitSelector::select_output)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}

impl<'a> DoubleEndedIterator for IterRef<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_at_back(1, IterBitSelector::select_output)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }
}

impl<'a> IterRef<'a> {
    #[inline]
    pub fn next_n(&mut self, bit_count: usize) -> Option<&BitStr> {
        self.next_at_front(bit_count, IterSliceSelector::select_output)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    pub fn next_n_back(&mut self, bit_count: usize) -> Option<&BitStr> {
        self.next_at_back(bit_count, IterSliceSelector::select_output)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    pub fn next_primitive<P: BitsPrimitive>(&mut self) -> Option<&Primitive<P>> {
        self.next_at_front(P::BIT_COUNT, IterPrimitiveSelector::<P>::select_output)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    pub fn next_primitive_back<P: BitsPrimitive>(&mut self) -> Option<&Primitive<P>> {
        self.next_at_back(P::BIT_COUNT, IterPrimitiveSelector::<P>::select_output)
            .map(|repr| unsafe { std::mem::transmute(repr) })
    }

    #[inline]
    fn next_at_front<F, R>(&mut self, bit_count: usize, f: F) -> Option<R>
    where
        F: FnOnce(SelectOutputArgs) -> R,
    {
        (self.end_offset - self.start_offset >= bit_count).then(|| {
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
        (self.end_offset - self.start_offset >= bit_count).then(|| {
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
}
impl<'a> ExactSizeIterator for IterRef<'a> {}

impl<'a> FusedIterator for IterRef<'a> {}

struct SelectOutputArgs {
    ptr: NonNull<()>,
    underlying_primitive: BitsPrimitiveDiscriminant,
    offset: usize,
    bit_count: usize,
}

trait SelectOutput: BitsPrimitiveSelector {
    fn select_output(args: SelectOutputArgs) -> <Self as BitsPrimitiveSelector>::Output;
}

struct IterBitSelector {
    ptr: NonNull<()>,
    offset: usize,
}
impl SelectOutput for IterBitSelector {
    fn select_output(args: SelectOutputArgs) -> <Self as BitsPrimitiveSelector>::Output {
        args.underlying_primitive.select(IterBitSelector {
            ptr: args.ptr,
            offset: args.offset,
        })
    }
}
impl BitsPrimitiveSelector for IterBitSelector {
    type Output = RefRepr;
    #[inline]
    fn select<U: BitsPrimitive>(self) -> Self::Output {
        let components = TypedRefComponents::new_normalized(self.ptr.cast::<U>(), self.offset, 1);
        components.encode()
    }
}

struct IterSliceSelector {
    ptr: NonNull<()>,
    offset: usize,
    bit_count: usize,
}
impl SelectOutput for IterSliceSelector {
    fn select_output(args: SelectOutputArgs) -> <Self as BitsPrimitiveSelector>::Output {
        args.underlying_primitive.select(IterSliceSelector {
            ptr: args.ptr,
            offset: args.offset,
            bit_count: args.bit_count,
        })
    }
}
impl BitsPrimitiveSelector for IterSliceSelector {
    type Output = RefRepr;
    #[inline]
    fn select<U: BitsPrimitive>(self) -> Self::Output {
        let components =
            TypedRefComponents::new_normalized(self.ptr.cast::<U>(), self.offset, self.bit_count);
        components.encode()
    }
}

struct IterPrimitiveSelector<P> {
    ptr: NonNull<()>,
    offset: usize,
    phantom: PhantomData<P>,
}
impl<P: BitsPrimitive> SelectOutput for IterPrimitiveSelector<P> {
    fn select_output(args: SelectOutputArgs) -> <Self as BitsPrimitiveSelector>::Output {
        args.underlying_primitive
            .select(IterPrimitiveSelector::<P> {
                ptr: args.ptr,
                offset: args.offset,
                phantom: PhantomData,
            })
    }
}
impl<P: BitsPrimitive> BitsPrimitiveSelector for IterPrimitiveSelector<P> {
    type Output = RefRepr;
    #[inline]
    fn select<U: BitsPrimitive>(self) -> Self::Output {
        let components =
            TypedRefComponents::new_normalized(self.ptr.cast::<U>(), self.offset, P::BIT_COUNT);
        components.encode()
    }
}

#[cfg(test)]
mod tests {
    use crate::BitStr;
    use crate::BitValue::{One, Zero};

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
}
