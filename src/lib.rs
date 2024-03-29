//! Rust Bits
//!
//! # Endianess
//!
//! This library follows a rule that determines that lower significance bits/bytes
//! always come first higher significance ones. For this reason, it may be
//! considered little-endian-friendly.
//!
//! However, wider types never have their individual bytes addressed directly. It
//! means that, when iterating over the bits of a `u16` value, the bits 0 to 7
//! come before the bits 8 to 15, regardless of the architecture endianness. So
//! this lib may in fact be considered endianness-neutral.
//!
//! If you want to have the bits 8 to 15 of a `u16` value come first, you must
//! explicitly [swap its bytes](u16::swap_bytes).

#[cfg(test)]
macro_rules! bitstring {
    ($str:expr) => {
        $str.parse::<$crate::BitString>().unwrap()
    };
}

#[cfg(test)]
macro_rules! assert_bitstring {
    ($value:expr, $expected:expr) => {{
        let bit_string: &$crate::BitString = &$value;
        assert_eq!(
            bit_string.buffer.len(),
            $crate::utils::required_bytes(bit_string.offset, bit_string.bit_count),
            "used bytes count"
        );
        assert_eq!(*bit_string, $expected);
    }};
}

mod bit;
mod bitsource;
mod bitsprimitive;
mod bitstr;
mod bitstring;
mod bitvalue;
mod copy_bits;
pub mod iter;
mod primitive;
mod ref_encoding;
mod utils;

pub use bit::*;
pub use bitsource::*;
pub use bitsprimitive::*;
pub use bitstr::*;
pub use bitstring::*;
pub use bitvalue::*;
pub use primitive::*;
