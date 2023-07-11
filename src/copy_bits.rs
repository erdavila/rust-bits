use std::cmp;

use crate::refrepr::{Offset, TypedPointer};
use crate::utils::{normalize_ptr_and_offset, BitPattern, CountedBits};
use crate::BitsPrimitive;

/// Copies bits.
///
/// # Panics
///
/// It panics in any of the following conditions:
/// * the source bits range defined by the `src_offset` and `bit_count`
/// parameters are not fully in the `src` slice;
/// * the destination bits range defined by the `dst_offset` and `bit_count`
/// parameters are not fully in the `dst` slice;
pub fn copy_bits<S: BitsPrimitive, D: BitsPrimitive>(
    src: &[S],
    src_offset: usize,
    dst: &mut [D],
    dst_offset: usize,
    bit_count: usize,
) {
    assert!(
        validate_range(src, src_offset, bit_count),
        "the source bits range must be fully contained in the source slice"
    );
    assert!(
        validate_range(dst, dst_offset, bit_count),
        "the destination bits range must be fully contained in the destination slice"
    );

    unsafe {
        copy_bits_raw(
            src.as_ptr(),
            src_offset,
            dst.as_mut_ptr(),
            dst_offset,
            bit_count,
        )
    };
}

/// Copies bits.
///
/// # Safety
///
/// Consider:
/// * source region: region of memory composed of contiguous `S` values
/// beginning at `src` and containing  at least `src_offset + bit_count` bits,
/// rounded up to consider full `S` values.
/// * destination region: region of memory composed of contiguous `D` values
/// beginning at `dst` and containing  at least `dst_offset + bit_count` bits,
/// rounded up to consider full `D` values.
///
/// Behavior is undefined if any of the following conditions are violated:
/// * The source region must be [valid] for reads.
/// * The destination region must be [valid] for writes.
/// * Both `src` and `dst` must be properly aligned.
/// * Both regions must *not* overlap.
///
/// [valid]: std::ptr#safety
pub unsafe fn copy_bits_raw<S: BitsPrimitive, D: BitsPrimitive>(
    src: *const S,
    src_offset: usize,
    dst: *mut D,
    dst_offset: usize,
    mut bit_count: usize,
) {
    if bit_count == 0 {
        return;
    }

    let mut source = Source::new(src, src_offset);
    let mut destination = Destination::new(dst, dst_offset);

    while bit_count > 0 {
        let bits = source.read(bit_count);
        bit_count -= bits.count;
        destination.write(bits);
    }

    destination.write_remainder();
}

fn validate_range<P: BitsPrimitive>(data: &[P], offset: usize, bit_count: usize) -> bool {
    let slice_bit_count = data.len() * P::BIT_COUNT;
    let bit_range_end = offset + bit_count;
    bit_range_end <= slice_bit_count
}

struct Source<P: BitsPrimitive> {
    ptr: TypedPointer<P>,
    buffer: CountedBits<P>,
}

impl<P: BitsPrimitive> Source<P> {
    pub fn new(ptr: *const P, offset: usize) -> Self {
        let (ptr, offset) = unsafe { normalize_ptr_and_offset((ptr as *mut P).into(), offset) };
        let mut buffer = CountedBits::from(unsafe { ptr.read() });
        buffer.drop_lsb(offset.value());

        Source { ptr, buffer }
    }

    pub fn read(&mut self, bit_count: usize) -> CountedBits<usize> {
        if self.buffer.count == 0 {
            let bits = unsafe {
                self.ptr = self.ptr.add(1);
                self.ptr.read()
            };
            self.buffer = CountedBits::from(bits);
        }

        let to_return = self.buffer.pop_lsb(cmp::min(bit_count, usize::BIT_COUNT));
        to_return.to_usize()
    }
}

struct Destination<P: BitsPrimitive> {
    ptr: TypedPointer<P>,
    offset: Offset<P>,
    buffer: CountedBits<P>,
}

impl<P: BitsPrimitive> Destination<P> {
    pub fn new(ptr: *mut P, offset: usize) -> Self {
        let (ptr, offset) = unsafe { normalize_ptr_and_offset(ptr.into(), offset) };
        Destination {
            ptr,
            offset,
            buffer: CountedBits::new(),
        }
    }

    pub fn write(&mut self, mut bits: CountedBits<usize>) {
        while bits.count > 0 {
            let popped_bits = bits.pop_lsb(self.buffer.room());
            let popped_bits = CountedBits::from_usize(popped_bits);
            self.buffer.push_msb(popped_bits);

            if self.offset.value() > 0 {
                let bit_count_to_write = P::BIT_COUNT - self.offset.value();
                if self.buffer.count >= bit_count_to_write {
                    let bits_to_write = self.buffer.pop_lsb(bit_count_to_write);
                    debug_assert!(bits_to_write.count == bit_count_to_write);
                    self.write_next_elem_keeping_surrounding_bits(bits_to_write);
                }
            } else if self.buffer.is_full() {
                self.write_next_elem(self.buffer.bits);
                self.buffer.clear();
            }
        }
    }

    pub fn write_remainder(mut self) {
        if self.buffer.count > 0 {
            self.write_next_elem_keeping_surrounding_bits(self.buffer);
        }
    }

    fn write_next_elem(&mut self, bits: P) {
        unsafe {
            self.ptr.write(bits);
            self.ptr = self.ptr.add(1);
        }
    }

    fn write_next_elem_keeping_surrounding_bits(&mut self, bits: CountedBits<P>) {
        let lsb_keep_bit_count = self.offset;

        let mut elem_bits = unsafe { self.ptr.read() };
        elem_bits &= BitPattern::new_with_ones()
            .and_zeros(bits.count)
            .and_ones(lsb_keep_bit_count.value())
            .get();
        elem_bits |= bits.bits << self.offset.value();
        self.write_next_elem(elem_bits);

        self.offset = Offset::new(0);
    }
}

#[cfg(test)]
mod tests {
    use std::slice;

    use crate::BitsPrimitive;

    use super::copy_bits;

    #[test]
    fn validate_range() {
        fn test_type<P: BitsPrimitive>() {
            use super::validate_range;

            assert!(validate_range(&[P::ZERO; 0], 0, 0));
            assert!(!validate_range(&[P::ZERO; 0], 0, 1));
            assert!(!validate_range(&[P::ZERO; 0], 1, 0));

            assert!(validate_range(&[P::ZERO; 1], 0, 0));
            assert!(validate_range(&[P::ZERO; 1], 0, P::BIT_COUNT));
            assert!(!validate_range(&[P::ZERO; 1], 0, P::BIT_COUNT + 1));
            assert!(validate_range(&[P::ZERO; 1], P::BIT_COUNT - 1, 0));
            assert!(validate_range(&[P::ZERO; 1], P::BIT_COUNT - 1, 1));
            assert!(!validate_range(&[P::ZERO; 1], P::BIT_COUNT - 1, 2));
            assert!(validate_range(&[P::ZERO; 1], P::BIT_COUNT, 0));
            assert!(!validate_range(&[P::ZERO; 1], P::BIT_COUNT, 1));
            assert!(!validate_range(&[P::ZERO; 1], P::BIT_COUNT + 1, 0));
        }

        test_type::<usize>();
        test_type::<u8>();
        test_type::<u16>();
        test_type::<u32>();
        test_type::<u64>();
        test_type::<u128>();
    }

    #[test]
    fn trivial() {
        macro_rules! assert_copy {
            ($type:ty) => {
                let src: $type = 0x_7766554433221100_FEDCBA9876543210_u128 as $type;
                let mut dst: $type = 0;

                copy_bits(
                    slice::from_ref(&src),
                    0,
                    slice::from_mut(&mut dst),
                    0,
                    <$type>::BIT_COUNT,
                );

                assert_eq!(dst, src);
            };
        }

        assert_copy!(usize);
        assert_copy!(u8);
        assert_copy!(u16);
        assert_copy!(u32);
        assert_copy!(u64);
        assert_copy!(u128);
    }

    #[test]
    fn multiple_elements() {
        macro_rules! assert_copy {
            ($type:ty) => {
                let src: [$type; 2] = [
                    0x_7766554433221100_FEDCBA9876543210_u128 as $type,
                    0x_5444333222111000_FFEEDDCCBBAA9988_u128 as $type,
                ];
                let mut dst: [$type; 2] = [0, 0];

                copy_bits(&src, 0, &mut dst, 0, 2 * <$type>::BIT_COUNT);

                assert_eq!(dst, src);
            };
        }

        assert_copy!(usize);
        assert_copy!(u8);
        assert_copy!(u16);
        assert_copy!(u32);
        assert_copy!(u64);
        assert_copy!(u128);
    }

    #[test]
    fn small_to_large() {
        let src = [0xEFu8, 0xCDu8, 0xABu8, 0x89u8]; // In memory: 89ABCDEF
        let mut dst = 0x_7766554433221100_FEDCBA9876543210_u128;

        copy_bits(&src, 4, slice::from_mut(&mut dst), 52, 24);

        assert_eq!(dst, 0x_77665544332219AB_CDECBA9876543210_u128);
    }

    #[test]
    fn large_to_small() {
        let src = 0x_7766554433221100_FEDCBA9876543210_u128;
        let mut dst: [u8; 14] = [
            0xFF, 0xEE, 0xDD, 0xCC, 0xBB, 0xAA, 0x89, 0x67, 0x45, 0x23, 0x01, 0xEF, 0xCD, 0xAB,
        ]; // In memory: ABCDEF0123456789AABBCCDDEEFF

        copy_bits(slice::from_ref(&src), 12, &mut dst, 4, 104);

        assert_eq!(
            dst,
            [0x3F, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0xA6]
        ); // In memory: A6554433221100FEDCBA9876543F
    }

    #[test]
    fn large_offsets() {
        let src: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: FEDCBA
        let mut dst: [u16; 2] = [0x5432, 0x9876]; // In memory: 98765432

        copy_bits(&src, 12, &mut dst, 20, 8);

        assert_eq!(dst, [0x5432, 0x9ED6]); // In memory: 9ED65432
    }
}
