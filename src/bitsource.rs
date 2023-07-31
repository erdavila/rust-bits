use crate::bitsprimitive::BitsPrimitive;
use crate::bitstr::BitStr;
use crate::copy_bits::{copy_bits, copy_primitives_to_bits, Destination};
use crate::ref_encoding::bit_pointer::BitPointer;
use crate::utils::CountedBits;
use crate::{BitString, BitValue};

pub trait BitSource {
    fn bit_count(&self) -> usize;

    /// # Safety
    unsafe fn copy_bits_to(&self, dst: BitPointer);
}

macro_rules! forward_methods_as_array {
    () => {
        #[inline]
        fn bit_count(&self) -> usize {
            BitSource::bit_count(&[*self])
        }

        #[inline]
        unsafe fn copy_bits_to(&self, dst: BitPointer) {
            BitSource::copy_bits_to(&[*self], dst);
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
        unsafe fn copy_bits_to(&self, dst: BitPointer) {
            BitSource::copy_bits_to(&self.as_ref(), dst);
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
    unsafe fn copy_bits_to(&self, dst: BitPointer) {
        let mut destination = Destination::bits(dst);
        for bit in self.iter().copied() {
            let bit = match bit {
                BitValue::Zero => 0,
                BitValue::One => 1,
            };
            destination.write(CountedBits::with_count(bit, 1));
        }
        destination.write_remainder();
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
    unsafe fn copy_bits_to(&self, dst: BitPointer) {
        copy_primitives_to_bits(self, dst, self.bit_count());
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
    unsafe fn copy_bits_to(&self, dst: BitPointer) {
        let components = self.ref_components();
        copy_bits(components.bit_ptr, dst, components.bit_count);
    }
}
