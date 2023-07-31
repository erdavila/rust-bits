use std::fmt::{Binary, Debug, Display, LowerHex, UpperHex, Write};

use crate::bitstr::ConsumeIterator;
use crate::{BitStr, BitValue, BitsPrimitive};

impl BitStr {
    fn fmt_hex(&self, f: &mut std::fmt::Formatter<'_>, upper: bool) -> std::fmt::Result {
        const BITS_PER_HEX_DIGIT: usize = 4;
        let bits_count = self.len();

        let remainder_bin_bits_count = bits_count % BITS_PER_HEX_DIGIT;
        let hex_digits_count = bits_count / BITS_PER_HEX_DIGIT;
        let hex_bits_count = bits_count - remainder_bin_bits_count;

        let (remainder_bin_bits, hex_bits) = self.split_at(hex_bits_count);

        if remainder_bin_bits_count > 0 {
            Binary::fmt(remainder_bin_bits, f)?;
            f.write_char(':')?;
        }

        struct Consumer {
            hex_digits: String,
            non_primitive_bits: usize,
            non_primitive_bit_count: usize,
            upper: bool,
        }
        impl Consumer {
            #[inline]
            fn format_hex<P: BitsPrimitive>(&self, value: P, width: usize) -> String {
                if self.upper {
                    format!("{:0width$X}", value, width = width)
                } else {
                    format!("{:0width$x}", value, width = width)
                }
            }
        }
        impl ConsumeIterator<'_> for Consumer {
            #[inline]
            fn consume_primitive<P: BitsPrimitive>(&mut self, value: P) -> Result<(), ()> {
                let str = self.format_hex(value, P::BIT_COUNT / BITS_PER_HEX_DIGIT);
                self.hex_digits.insert_str(0, &str);
                Ok(())
            }

            #[inline]
            fn consume_remainder_bit(&mut self, value: BitValue) -> Result<(), ()> {
                if value == BitValue::One {
                    self.non_primitive_bits |= 1 << self.non_primitive_bit_count;
                }
                self.non_primitive_bit_count += 1;

                if self.non_primitive_bit_count == BITS_PER_HEX_DIGIT {
                    let str = self.format_hex(self.non_primitive_bits, 1);
                    self.hex_digits.insert_str(0, &str);
                }

                Ok(())
            }
        }

        let mut consumer = Consumer {
            hex_digits: String::with_capacity(hex_digits_count),
            non_primitive_bits: 0,
            non_primitive_bit_count: 0,
            upper,
        };
        consumer.consume_iterator(hex_bits.iter()).unwrap();

        if f.alternate() && !consumer.hex_digits.is_empty() {
            f.write_str("0x")?;
        }

        f.write_str(&consumer.hex_digits)
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
        struct Consumer {
            bits: String,
        }
        impl ConsumeIterator<'_> for Consumer {
            #[inline]
            fn consume_primitive<P: BitsPrimitive>(&mut self, value: P) -> Result<(), ()> {
                let s = format!("{:0width$b}", value, width = P::BIT_COUNT);
                self.bits.insert_str(0, &s);
                Ok(())
            }

            #[inline]
            fn consume_remainder_bit(&mut self, value: BitValue) -> Result<(), ()> {
                let s = match value {
                    BitValue::Zero => "0",
                    BitValue::One => "1",
                };
                self.bits.insert_str(0, s);
                Ok(())
            }
        }

        let iter = self.iter();
        let mut consumer = Consumer {
            bits: String::with_capacity(iter.len()),
        };
        consumer.consume_iterator(iter).unwrap();

        if f.alternate() && !consumer.bits.is_empty() {
            f.write_str("0b")?;
        }

        f.write_str(&consumer.bits)
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
