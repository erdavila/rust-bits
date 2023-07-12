use crate::bitsprimitive::BitsPrimitive;
use crate::bitstr::BitStr;
use crate::copy_bits::copy_bits_ptr;
use crate::refrepr::{BitPointer, Offset, RefComponentsSelector, TypedPointer, TypedRefComponents};
use crate::utils::CountedBits;
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

        let (mut dst, offset) = {
            let bit_ptr = BitPointer::new_normalized(dst, offset);
            (bit_ptr.elem_ptr(), bit_ptr.offset().value())
        };

        if offset != 0 {
            let mut primitive_bits = CountedBits::with_count(dst.read(), offset);
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
        let src = BitPointer::new((*self).into(), Offset::new(0));
        let dst = BitPointer::new_normalized(dst, offset);
        copy_bits_ptr(src, dst, self.bit_count());
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
            struct Selector<D: BitsPrimitive>(BitPointer<D>);
            impl<D: BitsPrimitive> RefComponentsSelector for Selector<D> {
                type Output = ();

                #[inline]
                fn select<U: BitsPrimitive>(
                    self,
                    components: TypedRefComponents<U>,
                ) -> Self::Output {
                    let src = components.bit_ptr;
                    let dst = self.0;
                    unsafe {
                        copy_bits_ptr(src, dst, components.bit_count);
                    };
                }
            }

            Selector(BitPointer::new_normalized(dst, offset))
        })
    }
}
