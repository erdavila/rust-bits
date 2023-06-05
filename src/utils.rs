use crate::PrimitiveType;

pub(crate) fn make_bits_pattern<P: PrimitiveType>(
    blocks_len: impl IntoIterator<Item = usize>,
) -> P {
    let mut bits = P::ZERO;
    let mut parity = false;

    for block_len in blocks_len {
        bits = !bits << block_len;
        parity = !parity;
    }

    if parity {
        bits = !bits;
    }

    bits
}

#[cfg(test)]
mod tests {
    #[test]
    fn make_bits_pattern() {
        use super::make_bits_pattern;

        assert_eq!(make_bits_pattern::<u16>([]), 0b0);
        assert_eq!(make_bits_pattern::<u16>([2]), 0b011);
        assert_eq!(make_bits_pattern::<u16>([2, 3]), 0b011000);
        assert_eq!(make_bits_pattern::<u16>([2, 3, 4]), 0b0110001111);
    }
}
