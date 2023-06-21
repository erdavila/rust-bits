use std::marker::PhantomData;

use crate::copy_bits::copy_bits_raw;
use crate::refrepr::{RefComponentsSelector, RefRepr, TypedRefComponents};
use crate::BitsPrimitive;

#[repr(C)]
pub struct Primitive<P: BitsPrimitive> {
    _phantom: PhantomData<P>,
    _unsized: [()],
}

impl<P: BitsPrimitive> Primitive<P> {
    #[inline]
    pub fn read(&self) -> P {
        struct Selector<P>(PhantomData<P>);
        impl<P: BitsPrimitive> RefComponentsSelector for Selector<P> {
            type Output = P;
            #[inline]
            fn select<U: BitsPrimitive>(self, components: TypedRefComponents<U>) -> Self::Output {
                debug_assert!(components.bit_count == P::BIT_COUNT);
                let mut value = P::ZERO;
                unsafe {
                    copy_bits_raw(
                        components.ptr.as_ptr(),
                        components.offset,
                        &mut value,
                        0,
                        P::BIT_COUNT,
                    );
                }
                value
            }
        }

        let repr: RefRepr = unsafe { std::mem::transmute(self) };
        repr.decode().select(Selector::<P>(PhantomData))
    }
}

#[cfg(test)]
mod tests {
    use std::ptr::NonNull;

    use crate::refrepr::TypedRefComponents;
    use crate::{BitsPrimitive, Primitive};

    #[test]
    fn read() {
        let memory: [u16; 2] = [0xDCBA, 0x10FE]; // In memory:: 10FEDCBA
        let ptr = NonNull::from(&memory[0]);
        let components = TypedRefComponents {
            ptr,
            offset: 12,
            bit_count: u8::BIT_COUNT,
        };
        let repr = components.encode();
        let p_ref: &Primitive<u8> = unsafe { std::mem::transmute(repr) };

        let value = p_ref.read();

        assert_eq!(value, 0xED);
    }
}
