use std::cmp;

use crate::ref_encoding::bit_pointer::BitPointer;
use crate::ref_encoding::pointer::Pointer;
use crate::utils::{BitPattern, CountedBits};
use crate::{BitValue, BitsPrimitive};

pub trait Destination {
    fn write(&mut self, bits: CountedBits<u8>);
    fn write_remainder(self);
}

#[inline]
pub(crate) unsafe fn copy_bits(src: BitPointer, dst: BitPointer, bit_count: usize) {
    let src = PrimitivesSource::bits(src, bit_count);
    let dst = PrimitivesDestination::bits(dst);
    copy_bits_loop(src, dst);
}

pub(crate) unsafe fn copy_bits_to_primitives<P: BitsPrimitive>(
    bit_ptr: BitPointer,
    primitives: &mut [P],
    bit_count: usize,
) {
    let src = PrimitivesSource::bits(bit_ptr, bit_count);
    let dst = PrimitivesDestination::primitives(Pointer::from(primitives));
    copy_bits_loop(src, dst);
}

pub(crate) unsafe fn copy_primitives_to_bits<P: BitsPrimitive>(
    primitives: &[P],
    bit_ptr: BitPointer,
    bit_count: usize,
) {
    let src = PrimitivesSource::primitives_partial(Pointer::from(primitives), bit_count);
    let dst = PrimitivesDestination::bits(bit_ptr);
    copy_bits_loop(src, dst);
}

#[inline]
pub(crate) fn copy_bits_loop(
    src: impl Iterator<Item = CountedBits<u8>>,
    mut dst: impl Destination,
) {
    for bits in src {
        dst.write(bits);
    }

    dst.write_remainder();
}

pub(crate) struct PrimitivesSource<P: BitsPrimitive> {
    ptr: Pointer<P>,
    offset: usize,
    bit_count: usize,
    buffer: CountedBits<P>,
}
impl PrimitivesSource<u8> {
    #[inline]
    pub(crate) unsafe fn bits(bit_ptr: BitPointer, bit_count: usize) -> Self {
        PrimitivesSource {
            ptr: bit_ptr.byte_ptr(),
            offset: bit_ptr.offset().value(),
            bit_count,
            buffer: CountedBits::new(),
        }
    }
}
impl<P: BitsPrimitive> PrimitivesSource<P> {
    #[inline]
    pub(crate) unsafe fn primitives(ptr: Pointer<P>, count: usize) -> Self {
        Self::primitives_partial(ptr, count * P::BIT_COUNT)
    }

    #[inline]
    unsafe fn primitives_partial(ptr: Pointer<P>, bit_count: usize) -> Self {
        PrimitivesSource {
            ptr,
            offset: 0,
            bit_count,
            buffer: CountedBits::new(),
        }
    }
}
impl<P: BitsPrimitive> Iterator for PrimitivesSource<P> {
    type Item = CountedBits<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        (self.bit_count > 0).then(|| {
            if self.buffer.count == 0 {
                let primitive = unsafe { self.ptr.read() };
                self.ptr = unsafe { self.ptr.add(1) };

                self.buffer = CountedBits::from(primitive);
                if self.offset > 0 {
                    self.buffer.drop_lsb(self.offset);
                    self.offset = 0;
                }
            }

            let wanted_bits_count = cmp::min(self.bit_count, u8::BIT_COUNT);
            let mut result = self.buffer.pop_lsb(wanted_bits_count).to_u8();
            self.bit_count -= result.count;

            result.clear_uncounted_bits();
            result
        })
    }
}

pub(crate) fn bit_values_source(
    iter: impl IntoIterator<Item = BitValue>,
) -> impl Iterator<Item = CountedBits<u8>> {
    iter.into_iter().map(|bit| {
        let bit = match bit {
            BitValue::Zero => 0,
            BitValue::One => 1,
        };
        CountedBits::with_count(bit, 1)
    })
}

pub(crate) struct PrimitivesDestination<P: BitsPrimitive> {
    ptr: Pointer<P>,
    offset: usize,
    buffer: CountedBits<P>,
}
impl PrimitivesDestination<u8> {
    #[inline]
    pub(crate) unsafe fn bits(bit_ptr: BitPointer) -> Self {
        PrimitivesDestination {
            ptr: bit_ptr.byte_ptr(),
            offset: bit_ptr.offset().value(),
            buffer: CountedBits::new(),
        }
    }
}
impl<P: BitsPrimitive> PrimitivesDestination<P> {
    #[inline]
    unsafe fn primitives(ptr: Pointer<P>) -> Self {
        PrimitivesDestination {
            ptr,
            offset: 0,
            buffer: CountedBits::new(),
        }
    }
}
impl<P: BitsPrimitive> Destination for PrimitivesDestination<P> {
    fn write(&mut self, mut bits: CountedBits<u8>) {
        let bits_to_write = P::BIT_COUNT - self.offset;
        if self.buffer.count + bits.count >= bits_to_write {
            let moved_bits = bits.pop_lsb(bits_to_write - self.buffer.count);
            self.buffer.push_msb(CountedBits::from_u8(moved_bits));

            if self.offset > 0 {
                let primitive_ref = unsafe { self.ptr.as_mut() };
                *primitive_ref &= BitPattern::new_with_zeros().and_ones(self.offset).get();
                *primitive_ref |= self.buffer.bits << self.offset;
            } else {
                unsafe { self.ptr.write(self.buffer.bits) };
            }

            self.ptr = unsafe { self.ptr.add(1) };
            self.offset = 0;
            self.buffer = CountedBits::from_u8(bits);
        } else {
            self.buffer.push_msb(CountedBits::from_u8(bits));
        }
    }

    fn write_remainder(mut self) {
        if self.buffer.count > 0 {
            let primitive_ref = unsafe { self.ptr.as_mut() };
            *primitive_ref &= BitPattern::new_with_ones()
                .and_zeros(self.buffer.count)
                .and_ones(self.offset)
                .get();
            *primitive_ref |= self.buffer.bits << self.offset;
        }
    }
}

#[cfg(test)]
mod tests {
    mod source {
        use crate::copy_bits::PrimitivesSource;
        use crate::ref_encoding::bit_pointer::BitPointer;
        use crate::ref_encoding::byte_pointer::BytePointer;
        use crate::ref_encoding::pointer::Pointer;
        use crate::utils::CountedBits;

        #[test]
        fn bits_aligned() {
            let bits = [0xEF, 0xCD];
            let byte_ptr = BytePointer::from(bits.as_slice());
            let bit_ptr = BitPointer::new_normalized(byte_ptr, 0);

            let mut source = unsafe { PrimitivesSource::bits(bit_ptr, 16) };

            assert_eq!(source.next(), Some(CountedBits::with_count(0xEF, 8)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0xCD, 8)));
            assert_eq!(source.next(), None);
        }

        #[test]
        fn bits_unaligned() {
            let bits = [0xEF, 0xCD, 0xAB, 0x89];
            let byte_ptr = BytePointer::from(bits.as_slice());
            let bit_ptr = BitPointer::new_normalized(byte_ptr, 4);

            let mut source = unsafe { PrimitivesSource::bits(bit_ptr, 24) };

            assert_eq!(source.next(), Some(CountedBits::with_count(0xE, 4)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0xCD, 8)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0xAB, 8)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0x9, 4)));
            assert_eq!(source.next(), None);
        }

        #[test]
        fn bits_single() {
            let bits = 0b01101100u8;
            let byte_ptr = BytePointer::from(&bits);
            let bit_ptr = BitPointer::new_normalized(byte_ptr, 2);

            let mut source = unsafe { PrimitivesSource::bits(bit_ptr, 4) };

            assert_eq!(source.next(), Some(CountedBits::with_count(0b1011, 4)));
            assert_eq!(source.next(), None);
        }

        #[test]
        fn bits_empty() {
            let byte_ptr = BytePointer::from([].as_slice());
            let bit_ptr = BitPointer::new_normalized(byte_ptr, 2);

            let mut source = unsafe { PrimitivesSource::bits(bit_ptr, 0) };

            assert_eq!(source.next(), None);
        }

        #[test]
        fn primitives() {
            let primitives: [u16; 2] = [0xCDEF, 0x89AB];
            let ptr = Pointer::from(primitives.as_slice());

            let mut source = unsafe { PrimitivesSource::primitives(ptr, 2) };

            assert_eq!(source.next(), Some(CountedBits::with_count(0xEF, 8)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0xCD, 8)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0xAB, 8)));
            assert_eq!(source.next(), Some(CountedBits::with_count(0x89, 8)));
            assert_eq!(source.next(), None);
        }
    }

    mod destination {
        use crate::copy_bits::{Destination, PrimitivesDestination};
        use crate::ref_encoding::bit_pointer::BitPointer;
        use crate::ref_encoding::pointer::Pointer;
        use crate::utils::CountedBits;

        #[test]
        fn bits_multiple() {
            let mut bits = [0x89, 0x67, 0x45, 0x23];
            let bit_ptr = BitPointer::new_normalized(Pointer::from(bits.as_mut_slice()), 4);

            let mut destination = unsafe { PrimitivesDestination::bits(bit_ptr) };
            destination.write(CountedBits::with_count(0xEF, 8));
            destination.write(CountedBits::with_count(0xD, 4));
            destination.write(CountedBits::with_count(0xBC, 8));
            destination.write(CountedBits::with_count(0xA, 4));
            destination.write_remainder();

            assert_eq!(bits, [0xF9, 0xDE, 0xBC, 0x2A]);
        }

        #[test]
        fn bits_single() {
            let mut bits = 0b10010011u8;
            let bit_ptr = BitPointer::new_normalized(Pointer::from(&mut bits), 2);

            let mut destination = unsafe { PrimitivesDestination::bits(bit_ptr) };
            destination.write(CountedBits::with_count(0b1, 1));
            destination.write(CountedBits::with_count(0b101, 3));
            destination.write_remainder();

            assert_eq!(bits, 0b10101111u8);
        }

        #[test]
        fn primitives() {
            let mut primitives = [0x6789u16, 0x2345u16];
            let ptr = Pointer::from(primitives.as_mut_slice());

            let mut destination = unsafe { PrimitivesDestination::primitives(ptr) };
            destination.write(CountedBits::with_count(0xF, 4));
            destination.write(CountedBits::with_count(0xDE, 8));
            destination.write(CountedBits::with_count(0xC, 4));
            destination.write(CountedBits::with_count(0xAB, 8));
            destination.write_remainder();

            assert_eq!(primitives, [0xCDEFu16, 0x23ABu16]);
        }
    }
}
