use std::fmt::{Binary, Debug, Display, LowerHex, UpperHex, Write};

use crate::bitstr::consume_iterator;
use crate::utils::CountedBits;
use crate::{BitStr, BitValue, BitsPrimitive};

impl BitStr {
    fn fmt_hex(&self, f: &mut std::fmt::Formatter<'_>, upper: bool) -> std::fmt::Result {
        const BITS_PER_HEX_DIGIT: usize = 4;
        let bits_count = self.len();

        let remainder_bin_bits_count = bits_count % BITS_PER_HEX_DIGIT;
        let hex_digits_count = bits_count / BITS_PER_HEX_DIGIT;
        let hex_bits_count = bits_count - remainder_bin_bits_count;

        let (remainder_bin_bits, hex_bits) = self.split_at(hex_bits_count);

        let format_hex = |value, width| {
            if upper {
                format!("{:0width$X}", value, width = width)
            } else {
                format!("{:0width$x}", value, width = width)
            }
        };

        struct State {
            hex_digits: String,
            non_primitive_bits: CountedBits<u8>,
        }
        let mut state = State {
            hex_digits: String::with_capacity(hex_digits_count),
            non_primitive_bits: CountedBits::new(),
        };
        let result: Result<_, ()> = consume_iterator(
            hex_bits.iter(),
            &mut state,
            |state, byte| {
                let str = format_hex(byte, u8::BIT_COUNT / BITS_PER_HEX_DIGIT);
                state.hex_digits.insert_str(0, &str);
                Ok(())
            },
            |state, bit| {
                state.non_primitive_bits.push_msb_value(bit);

                if state.non_primitive_bits.count == BITS_PER_HEX_DIGIT {
                    let str = format_hex(state.non_primitive_bits.bits, 1);
                    state.hex_digits.insert_str(0, &str);
                }

                Ok(())
            },
        );
        result.unwrap();

        if remainder_bin_bits_count > 0 {
            Binary::fmt(remainder_bin_bits, f)?;
            f.write_char(':')?;
        }

        if f.alternate() && !state.hex_digits.is_empty() {
            f.write_str("0x")?;
        }

        f.write_str(&state.hex_digits)
    }
}

impl Display for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Binary::fmt(self, f)
    }
}

impl Binary for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let iter = self.iter();
        let mut digits = String::with_capacity(iter.len());

        let result: Result<_, ()> = consume_iterator(
            iter,
            &mut digits,
            |digits, byte| {
                let s = format!("{:0width$b}", byte, width = u8::BIT_COUNT);
                digits.insert_str(0, &s);
                Ok(())
            },
            |digits, bit| {
                let s = match bit {
                    BitValue::Zero => "0",
                    BitValue::One => "1",
                };
                digits.insert_str(0, s);
                Ok(())
            },
        );
        result.unwrap();

        if f.alternate() && !digits.is_empty() {
            f.write_str("0b")?;
        }

        f.write_str(&digits)
    }
}

impl LowerHex for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_hex(f, false)
    }
}

impl UpperHex for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_hex(f, true)
    }
}

impl Debug for BitStr {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"")?;
        Display::fmt(self, f)?;
        write!(f, "\"")
    }
}

#[cfg(test)]
mod tests {
    use crate::BitStr;

    #[test]
    fn display() {
        let memory: [u8; 2] = [0b00101011, 0b00101110];
        let bit_str = &BitStr::new_ref(memory.as_ref())[1..15];

        assert_eq!(format!("{}", bit_str), "01011100010101");
        assert_eq!(format!("{:#}", bit_str), "0b01011100010101");
        assert_eq!(format!("{}", &bit_str[..0]), "");
        assert_eq!(format!("{:#}", &bit_str[..0]), "");
    }

    #[test]
    fn binary() {
        let memory: [u8; 2] = [0b00101011, 0b00101110];
        let bit_str = &BitStr::new_ref(memory.as_ref())[1..15];

        assert_eq!(format!("{:b}", bit_str), "01011100010101");
        assert_eq!(format!("{:#b}", bit_str), "0b01011100010101");
        assert_eq!(format!("{:b}", &bit_str[..0]), "");
        assert_eq!(format!("{:#b}", &bit_str[..0]), "");
    }

    #[test]
    fn hex() {
        let memory: [u8; 3] = [0xBA, 0xDC, 0xFE]; // In memory: FEDCBA
        let bit_str = &BitStr::new_ref(memory.as_ref())[4..20]; // In memory: EDCB

        assert_eq!(format!("{:x}", bit_str), "edcb");
        assert_eq!(format!("{:x}", &bit_str[..15]), "110:dcb");
        assert_eq!(format!("{:x}", &bit_str[..14]), "10:dcb");
        assert_eq!(format!("{:x}", &bit_str[..13]), "0:dcb");
        assert_eq!(format!("{:x}", &bit_str[..12]), "dcb");
        assert_eq!(format!("{:x}", &bit_str[..4]), "b");
        assert_eq!(format!("{:x}", &bit_str[..3]), "011:");
        assert_eq!(format!("{:x}", &bit_str[..2]), "11:");
        assert_eq!(format!("{:x}", &bit_str[..1]), "1:");
        assert_eq!(format!("{:x}", &bit_str[..0]), "");

        assert_eq!(format!("{:#x}", bit_str), "0xedcb");
        assert_eq!(format!("{:#x}", &bit_str[..15]), "0b110:0xdcb");
        assert_eq!(format!("{:#x}", &bit_str[..14]), "0b10:0xdcb");
        assert_eq!(format!("{:#x}", &bit_str[..13]), "0b0:0xdcb");
        assert_eq!(format!("{:#x}", &bit_str[..12]), "0xdcb");
        assert_eq!(format!("{:#x}", &bit_str[..4]), "0xb");
        assert_eq!(format!("{:#x}", &bit_str[..3]), "0b011:");
        assert_eq!(format!("{:#x}", &bit_str[..2]), "0b11:");
        assert_eq!(format!("{:#x}", &bit_str[..1]), "0b1:");
        assert_eq!(format!("{:#x}", &bit_str[..0]), "");

        assert_eq!(format!("{:X}", bit_str), "EDCB");
        assert_eq!(format!("{:X}", &bit_str[..15]), "110:DCB");
        assert_eq!(format!("{:X}", &bit_str[..14]), "10:DCB");
        assert_eq!(format!("{:X}", &bit_str[..13]), "0:DCB");
        assert_eq!(format!("{:X}", &bit_str[..12]), "DCB");
        assert_eq!(format!("{:X}", &bit_str[..4]), "B");
        assert_eq!(format!("{:X}", &bit_str[..3]), "011:");
        assert_eq!(format!("{:X}", &bit_str[..2]), "11:");
        assert_eq!(format!("{:X}", &bit_str[..1]), "1:");
        assert_eq!(format!("{:X}", &bit_str[..0]), "");

        assert_eq!(format!("{:#X}", bit_str), "0xEDCB");
        assert_eq!(format!("{:#X}", &bit_str[..15]), "0b110:0xDCB");
        assert_eq!(format!("{:#X}", &bit_str[..14]), "0b10:0xDCB");
        assert_eq!(format!("{:#X}", &bit_str[..13]), "0b0:0xDCB");
        assert_eq!(format!("{:#X}", &bit_str[..12]), "0xDCB");
        assert_eq!(format!("{:#X}", &bit_str[..4]), "0xB");
        assert_eq!(format!("{:#X}", &bit_str[..3]), "0b011:");
        assert_eq!(format!("{:#X}", &bit_str[..2]), "0b11:");
        assert_eq!(format!("{:#X}", &bit_str[..1]), "0b1:");
        assert_eq!(format!("{:#X}", &bit_str[..0]), "");
    }

    #[test]
    fn debug() {
        let memory: [u8; 2] = [0b00101011, 0b00101110];
        let bit_str = &BitStr::new_ref(memory.as_ref())[1..15];

        assert_eq!(format!("{:?}", bit_str), "\"01011100010101\"");
        assert_eq!(format!("{:#?}", bit_str), "\"0b01011100010101\"");
        assert_eq!(format!("{:?}", &bit_str[..0]), "\"\"");
        assert_eq!(format!("{:#?}", &bit_str[..0]), "\"\"");
    }
}
