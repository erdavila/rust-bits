use crate::bitsprimitive::BitsPrimitive;
use crate::bitstr::BitStr;
use crate::copy_bits::copy_bits_raw;
use crate::refrepr::{RefComponentsSelector, TypedPointer, TypedRefComponents};
use crate::utils::{normalize_ptr_and_offset, CountedBits};
use crate::{BitString, BitValue};

pub trait BitSource {
    fn bit_count(&self) -> usize;

    /// # Safety
    ///
    /// TODO
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: TypedPointer<D>, offset: usize);
}

macro_rules! forward_methods_as_array {
    () => {
        #[inline]
        fn bit_count(&self) -> usize {
            BitSource::bit_count(&[*self])
        }

        #[inline]
        unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: TypedPointer<D>, offset: usize) {
            BitSource::copy_bits_to(&[*self], dst, offset);
        }
    };
}

macro_rules! forward_methods_as_ref {
    () => {
        #[inline]
        fn bit_count(&self) -> usize {
            BitSource::bit_count(&self.as_ref())
        }

        #[inline]
        unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: TypedPointer<D>, offset: usize) {
            BitSource::copy_bits_to(&self.as_ref(), dst, offset);
        }
    };
}

impl BitSource for BitValue {
    forward_methods_as_array!();
}

impl<const N: usize> BitSource for [BitValue; N] {
    forward_methods_as_ref!();
}

impl BitSource for &[BitValue] {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len()
    }

    #[inline]
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: TypedPointer<D>, offset: usize) {
        let mut iter = self.iter().copied();

        let (mut dst, offset) = normalize_ptr_and_offset(dst, offset);

        if offset.value() != 0 {
            let mut primitive_bits = CountedBits::with_count(dst.read(), offset.value());
            for bit in iter.by_ref() {
                primitive_bits.push_msb_value(bit);
                if primitive_bits.is_full() {
                    break;
                }
            }
            dst.write(primitive_bits.bits);
            dst = dst.add(1)
        }

        let mut primitive_bits = CountedBits::new();

        for bit in iter {
            primitive_bits.push_msb_value(bit);
            if primitive_bits.count == D::BIT_COUNT {
                dst.write(primitive_bits.bits);
                dst = dst.add(1);
                primitive_bits.clear();
            }
        }

        if primitive_bits.count > 0 {
            dst.write(primitive_bits.bits);
        }
    }
}

impl<P: BitsPrimitive> BitSource for P {
    forward_methods_as_array!();
}

impl<P: BitsPrimitive, const N: usize> BitSource for [P; N] {
    forward_methods_as_ref!();
}

impl<P: BitsPrimitive> BitSource for &[P] {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len() * P::BIT_COUNT
    }

    #[inline]
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: TypedPointer<D>, offset: usize) {
        copy_bits_raw(
            *self as *const [P] as *const P,
            0,
            dst.as_mut_ptr(),
            offset,
            self.bit_count(),
        );
    }
}

impl BitSource for &BitString {
    forward_methods_as_ref!();
}

impl BitSource for &BitStr {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len()
    }

    #[inline]
    unsafe fn copy_bits_to<D: BitsPrimitive>(&self, dst: TypedPointer<D>, offset: usize) {
        self.ref_components().select({
            struct Selector<D: BitsPrimitive> {
                dst: TypedPointer<D>,
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
                            components.offset.value(),
                            self.dst.as_mut_ptr(),
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
