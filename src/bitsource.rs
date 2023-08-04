use crate::bitsprimitive::BitsPrimitive;
use crate::bitstr::BitStr;
use crate::copy_bits::{
    bit_values_source, copy_bits_loop, Destination, PrimitivesDestination, PrimitivesSource,
};
use crate::ref_encoding::bit_pointer::BitPointer;
use crate::ref_encoding::pointer::Pointer;
use crate::{BitString, BitValue};

use self::private::PrivateBitSource;

mod private {
    use crate::copy_bits::Destination;

    pub trait PrivateBitSource {
        fn bit_count(&self) -> usize;
        fn copy_bits_to(self, dst: impl Destination);
    }
}

pub trait BitSource: private::PrivateBitSource + Sized {
    /// # Safety
    #[inline]
    unsafe fn copy_bits_to_bit_ptr(self, dst: BitPointer) {
        let dst = PrimitivesDestination::bits(dst);
        self.copy_bits_to(dst);
    }
}

macro_rules! forward_methods_as_array {
    () => {
        #[inline]
        fn bit_count(&self) -> usize {
            PrivateBitSource::bit_count(&[*self])
        }

        #[inline]
        fn copy_bits_to(self, dst: impl Destination) {
            PrivateBitSource::copy_bits_to([self], dst);
        }
    };
}

macro_rules! forward_methods_as_ref {
    () => {
        #[inline]
        fn bit_count(&self) -> usize {
            PrivateBitSource::bit_count(&self.as_ref())
        }

        #[inline]
        fn copy_bits_to(self, dst: impl Destination) {
            PrivateBitSource::copy_bits_to(self.as_ref(), dst);
        }
    };
}

impl BitSource for BitValue {}
impl PrivateBitSource for BitValue {
    forward_methods_as_array!();
}

impl<const N: usize> BitSource for [BitValue; N] {}
impl<const N: usize> PrivateBitSource for [BitValue; N] {
    forward_methods_as_ref!();
}

impl BitSource for &[BitValue] {}
impl PrivateBitSource for &[BitValue] {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len()
    }

    #[inline]
    fn copy_bits_to(self, dst: impl Destination) {
        let src = bit_values_source(self.iter().copied());
        copy_bits_loop(src, dst);
    }
}

impl<P: BitsPrimitive> BitSource for P {}
impl<P: BitsPrimitive> PrivateBitSource for P {
    forward_methods_as_array!();
}

impl<P: BitsPrimitive, const N: usize> BitSource for [P; N] {}
impl<P: BitsPrimitive, const N: usize> PrivateBitSource for [P; N] {
    forward_methods_as_ref!();
}

impl<P: BitsPrimitive> BitSource for &[P] {}
impl<P: BitsPrimitive> PrivateBitSource for &[P] {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len() * P::BIT_COUNT
    }

    #[inline]
    fn copy_bits_to(self, dst: impl Destination) {
        let src = unsafe { PrimitivesSource::primitives(Pointer::from(self), self.len()) };
        copy_bits_loop(src, dst);
    }
}

impl BitSource for &BitString {}
impl PrivateBitSource for &BitString {
    forward_methods_as_ref!();
}

impl BitSource for &BitStr {}
impl PrivateBitSource for &BitStr {
    #[inline]
    fn bit_count(&self) -> usize {
        self.len()
    }

    #[inline]
    fn copy_bits_to(self, dst: impl Destination) {
        let components = self.ref_components();
        let src = unsafe { PrimitivesSource::bits(components.bit_ptr, components.bit_count) };
        copy_bits_loop(src, dst);
    }
}
