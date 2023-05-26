use bit::Bit;

fn main() {
    let byte: u8 = 0b10010011;

    let bit0: &Bit = Bit::new_ref(&byte, 0);
    let bit1: &Bit = Bit::new_ref(&byte, 1);
    let bit2: &Bit = Bit::new_ref(&byte, 2);
    let bit3: &Bit = Bit::new_ref(&byte, 3);
    let bit4: &Bit = Bit::new_ref(&byte, 4);
    let bit5: &Bit = Bit::new_ref(&byte, 5);
    let bit6: &Bit = Bit::new_ref(&byte, 6);
    let bit7: &Bit = Bit::new_ref(&byte, 7);

    assert!(bit0.get());
    assert!(bit1.get());
    assert!(!bit2.get());
    assert!(!bit3.get());
    assert!(bit4.get());
    assert!(!bit5.get());
    assert!(!bit6.get());
    assert!(bit7.get());

    let mut byte = byte;

    let bit3: &mut Bit = Bit::new_mut(&mut byte, 3);
    bit3.set(true);

    let bit4: &mut Bit = Bit::new_mut(&mut byte, 4);
    bit4.set(false);

    assert_eq!(byte, 0b10001011);
}

mod bit {
    #[repr(transparent)]
    pub struct Bit {
        _unused_unsized: [()], // It is here just to make the struct unsized
    }

    struct DstRefParts<R> {
        raw_ref: R,
        length: usize,
    }

    impl Bit {
        pub fn new_ref(byte: &u8, bit_number: usize) -> &Bit {
            assert!(bit_number < 8);
            let parts = DstRefParts {
                raw_ref: byte,
                length: bit_number,
            };
            unsafe { std::mem::transmute(parts) }
        }

        pub fn new_mut(byte: &mut u8, bit_number: usize) -> &mut Bit {
            assert!(bit_number < 8);
            let parts = DstRefParts {
                raw_ref: byte,
                length: bit_number,
            };
            unsafe { std::mem::transmute(parts) }
        }

        pub fn get(&self) -> bool {
            let parts: DstRefParts<&u8> = unsafe { std::mem::transmute(self) };
            let byte = parts.raw_ref;
            let bit_number = parts.length;

            (*byte >> bit_number) & 0b00000001 != 0
        }

        pub fn set(&mut self, value: bool) {
            let parts: DstRefParts<&mut u8> = unsafe { std::mem::transmute(self) };
            let byte = parts.raw_ref;
            let bit_number = parts.length;

            let mask = 0b00000001 << bit_number;

            if value {
                *byte |= mask;
            } else {
                *byte &= !mask;
            }
        }
    }
}
