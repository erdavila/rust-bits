use std::ptr::NonNull;

use crate::bitsprimitive::BitsPrimitive;
use crate::bitstr::BitStr;
use crate::copy_bits::copy_bits_raw;
use crate::refrepr::{RefComponentsSelector, TypedRefComponents};
use crate::utils::CountedBits;
use crate::BitValue;

pub trait BitSource {
    fn bit_count(&self) -> usize;

    /// # Safety
    ///
    /// TODO
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: NonNull<D>, offset: usize);
}

impl BitSource for &[BitValue] {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len()
    }

    #[inline]
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: NonNull<D>, offset: usize) {
        debug_assert!(offset < D::BIT_COUNT);

        let (src_bits, mut dst) = if offset != 0 {
            todo!()
        } else {
            (*self, dst.as_ptr())
        };

        let mut primitive_bits = CountedBits::new();

        for bit in src_bits.iter().copied() {
            primitive_bits.push_msb_value(bit);
            if primitive_bits.count == D::BIT_COUNT {
                *dst = primitive_bits.bits;
                dst = dst.add(1);
                primitive_bits.clear();
            }
        }

        if primitive_bits.count > 0 {
            *dst = primitive_bits.bits;
        }
    }
}

impl<P: BitsPrimitive> BitSource for &[P] {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len() * P::BIT_COUNT
    }

    #[inline]
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: NonNull<D>, offset: usize) {
        copy_bits_raw(
            *self as *const [P] as *const P,
            0,
            dst.as_ptr(),
            offset,
            self.bit_count(),
        );
    }
}

impl BitSource for &BitStr {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len()
    }

    #[inline]
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: NonNull<D>, offset: usize) {
        self.ref_components().select({
            struct Selector<D> {
                dst: NonNull<D>,
                offset: usize,
            }
            impl<D: BitsPrimitive> RefComponentsSelector for Selector<D> {
                type Output = ();

                #[inline]
                fn select<U: BitsPrimitive>(
                    self,
                    components: TypedRefComponents<U>,
                ) -> Self::Output {
                    unsafe {
                        copy_bits_raw(
                            components.ptr.as_ptr(),
                            components.offset,
                            self.dst.as_ptr(),
                            self.offset,
                            components.bit_count,
                        )
                    };
                }
            }

            Selector { dst, offset }
        })
    }
}
