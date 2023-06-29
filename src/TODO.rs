impl BitsSource for BitValue {}
impl<const N: usize> BitsSource for [BitValue; N] {}
impl<const N: usize> BitsSource for &[BitValue; N] {}
impl BitsSource for &[BitValue] {}
impl BitsSource for &Bit {}
impl<P: BitsPrimitive> BitsSource for P {}
impl<P: BitsPrimitive, const N: usize> BitsSource for [P; N] {}
impl<P: BitsPrimitive, const N: usize> BitsSource for &[P; N] {}
impl<P: BitsPrimitive> BitsSource for &[P] {}
impl<P: BitsPrimitive> BitsSource for &Primitive<P> {}
impl BitsSource for BitString {}
impl BitsSource for &BitString {}
impl BitsSource for &BitStr {}

fn bit_string_construction() {
    BitString::new();
    BitString::default();
    Default::default();

    /*
        Parsing format:
            STRING := GROUPS_B
            GROUPS_B := '0b'? BIN_DIGITS (':' GROUPS_H)?
                      | '0x' HEX_DIGITS (':' GROUPS_B)?
            GROUPS_H := '0x'? HEX_DIGITS (':' GROUPS_B)?
                      | '0b' BIN_DIGITS (':' GROUPS_H)?
            BIN_DIGITS := (BIN_DIGIT | '_')*
            HEX_DIGITS := (HEX_DIGIT | '_')*
            BIN_DIGIT := '0' | '1'
            HEX_DIGIT := '0'..'1' | 'a'..'f' | 'A'..'F'

            A group of HEX_DIGITS starting with '0b' MUST be prefixed with '0x'.
            * This is not required if the starting digits are '0_b' or '_0b'.
            Otherwise, the '0b' is recognized as a binary digits indicator.
     */
    let bit_string = bit_string!(literal_string);
    let bit_string = bit_string!(literal_string, u8); // ... and other primitive types
    let _: Result<BitString, _> = str.parse();

    let msb: usize;
    let lsb: usize;
    BitString::with_reserved_space(msb, lsb);

    let bit: BitValue;
    let len: usize;
    BitString::repeat(bit, len);

    let source: impl BitsSource;
    BitString::from(source);

    let iterable: impl BitsSource;
    let iterable: impl Iterator<Item = BitValue>;
    let iterable: impl Iterator<Item = impl BitsPrimitive>;
    BitString::from_iter(iterable);

    bit_string.clone();

    bit_str.to_owned();

    let bits: Vec<BitValue>;
    let _: BitString = bits.iter().collect();
    let _: BitString = bits.into_iter().collect();
}

fn bit_str_construction() {
    let n: u8; // ... and other primitive types
    let bit_str: &BitStr = BitStr::new_ref(&n);
    let bit_str: &mut BitStr = BitStr::new_mut(&mut n);

    // Also for mut!
    let primitive_slice: &[u8]; // ... and other primitive types
    let bit_str: &BitStr = BitStr::new_ref(primitive_slice);

    // Also for mut!
    let p: &Primitive<u8>; // ... and other primitive types
    let bit_str: &BitStr = p.as_bit_str();
    let bit_str: &BitStr = p.as_ref();

    // Also for mut!
    let bit: &Bit;
    let bit_str: &BitStr = bit.as_bit_str();
    let bit_str: &BitStr = bit.as_ref();
}

fn inspecting() {
    let len: usize = bit_str.len();
    let is_empty: bool = bit_str.is_empty();

    let bit_str: &BitStr = bit_str.deref();
    let bit_str: &mut BitStr = bit_str.deref_mut();

    let bit_str: &BitStr = bit_str.borrow();
    let bit_str: &mut BitStr = bit_str.borrow_mut();

    let bit_str: &BitStr = bit_str.as_ref();
    let bit_str: &mut BitStr = bit_str.as_mut();
}

fn accessing() {
    let index: usize;
    let bit: Option<BitValue> = bit_str.get(index);
    let bit: Option<&Bit> = bit_str.get_ref(index);
    let bit: Option<&mut Bit> = bit_str.get_mut(index);

    let range: impl RangeBounds<usize>;
    let slice: Option<&BitStr> = bit_str.get_range_ref(range);
    let slice: Option<&mut BitStr> = bit_str.get_range_mut(range);

    let index: usize;
    let bit: Option<u8> = bit_str.get_primitive::<u8>(index); // ... and other primitive types
    let bit: Option<&Primitive<u8>> = bit_str.get_primitive_ref::<u8>(index); // ... and other primitive types
    let bit: Option<&mut Primitive<u8>> = bit_str.get_primitive_mut::<u8>(index); // ... and other primitive types

    // Also mut variations!
    // May panic
    let begin: usize;
    let end: usize;
    let bit_str: &BitStr = &bit_str[..];
    let bit_str: &BitStr = &bit_str[begin..];
    let bit_str: &BitStr = &bit_str[..end];
    let bit_str: &BitStr = &bit_str[..=end];
    let bit_str: &BitStr = &bit_str[begin..end];
    let bit_str: &BitStr = &bit_str[begin..=end];

    // Also mut variations!
    // May panic
    let index: usize;
    let bit: &Bit = &bit_str[index];

    let (msb, lsb): (&BitStr, &BitStr) = bit_str.split_at(index);

    let (msb, lsb): (&mut BitStr, &mut BitStr) = bit_str.split_at_mut(index);
}

fn adding() {
    fn source() -> impl BitsSource;
    let index: usize;
    bit_string.insert(index, source());

    fn source() -> impl BitsSource;
    bit_string.lsb().push(source());
}

fn removing() {
    let index: usize;
    let begin: usize;
    let end: usize;
    let removed: Option<BitValue> = bit_string.remove(index);
    let removed: Option<u8> = bit_string.remove(index); // ... and other primitive types
    let removed: Option<BitString> = bit_string.remove_n(begin..end);

    let count: usize;
    let popped: Option<BitValue> = bit_string.lsb().pop::<BitValue>();
    let popped: Option<u8> = bit_string.lsb().pop::<u8>(); // ... and other primitive types
    let popped: Option<BitString> = bit_string.lsb().pop_n(count);
    let popped: BitString = bit_string.lsb().pop_up_to(count);

    let bit: BitValue;
    let count: usize = bit_string.lsb().strip(bit);

    let count: usize;
    bit_string.lsb().discard(count);

    let len: usize;
    bit_string.lsb().truncate(len);

    bit_string.clear();
}

fn adding_or_removing() {
    let bit: BitValue;
    let new_len: usize;
    bit_string.lsb().resize(new_len, bit);
    assert_eq!(bs.len(), new_len);

    fn source() -> impl BitsSource;
    let removed: BitString = bit_string.splice(range, source());
    let removed: Option<BitString> = bit_str.replace(range, source()); // source must have same number of bits

    bit_str.fill(bit);
}

trait BitIterator: Iterator + DoubleEndedIterator + ExactSizeIterator + FusedIterator {
    type PrimitiveItem<P>;
    type SliceItem;

    fn next_primitive<P: BitsPrimitive>(&mut self) -> Option<Self::PrimitiveItem<P>>;
    fn next_n(&mut self, len: usize) -> Option<SliceItem>;
    fn rev(self) -> impl BitIterator;
    fn primitives<P: BitsPrimitive>(self) -> impl BitBlockIterator<Self::PrimitiveItem<P>, Self::SliceItem>;
    fn subslices(self, len: usize) -> impl BitBlockIterator<Self::SliceItem, Self::SliceItem>;
}

struct Iter {}
impl Iterator for Iter {
    type Item = BitValue;
}
impl BitIterator for Iter {
    type PrimitiveItem<P> = P;
    type SliceItem = &BitStr;
}

struct IterRef {}
impl Iterator for IterRef {
    type Item = &Bit;
}
impl BitIterator for IterRef {
    type PrimitiveItem<P> = &Primitive<P>;
    type SliceItem = &BitStr;
}

struct IterMut {}
impl Iterator for IterMut {
    type Item = &mut BitStr;
}
impl BitIterator for IterMut {
    type PrimitiveItem<P> = &mut Primitive<P>;
    type SliceItem = &mut BitStr;
}

struct IntoIter {}
impl Iterator for IntoIter {
    type Item = BitValue;
}
impl BitIterator for IntoIter {
    type PrimitiveItem<P> = P;
    type SliceItem = BitString;
}

fn iteration() {
    let iter: Iter = bit_str.iter();
    let iter: IterRef = bit_str.iter_ref();
    let iter: IterMut = bit_str.iter_mut();

    for bit_ref in bit_str {}
    for bit_value in bit_string {}
}

fn consumption() {
    let iter: IterRef = bit_str.into_iter();
    let iter: IntoIter = bit_string.into_iter();
}

trait BitBlockIterator<T, R>: Iterator<Item = T> + DoubleEndedIterator + ExactSizeIterator + FusedIterator {
    fn into_remainder(self) -> Option<R>;
}

fn primitives_iteration() {
    let iter = bit_str.iter().primitives::<u16>();
    let _: Option<u16> = iter.next();
    let _: Option<&BitStr> = iter.into_remainder();

    let iter = bit_str.iter_ref().primitives::<u16>();
    let _: Option<&Primitive<u16>> = iter.next();
    let _: Option<&BitStr> = iter.into_remainder();

    let iter = bit_str.iter_mut().primitives::<u16>();
    let _: Option<&mut Primitive<u16>> = iter.next();
    let _: Option<&mut BitStr> = iter.into_remainder();

    let iter = bit_str.into_iter().primitives::<u16>();
    let _: Option<u16> = iter.next();
    let _: Option<BitString> = iter.into_remainder();
}

fn subslices() {
    let iter = bit_str.iter().subslices(3);
    let _: Option<&BitStr> = iter.next();
    let _: Option<&BitStr> = iter.into_remainder();

    let iter = bit_str.iter_ref().subslices(3);
    let _: Option<&BitStr> = iter.next();
    let _: Option<&BitStr> = iter.into_remainder();

    let iter = bit_str.iter_mut().subslices(3);
    let _: Option<&mut BitStr> = iter.next();
    let _: Option<&mut BitStr> = iter.into_remainder();

    let iter = bit_str.into_iter().subslices(3);
    let _: Option<BitString> = iter.next();
    let _: Option<BitString> = iter.into_remainder();
}

fn reverse_iteration() {
    let s = bit_string!("x:ABCD");

    let iter = s.iter();
    assert_eq!(iter.next(), Some(BitValue::Zero)); // D: 010[0]
    assert_eq!(iter.next(), Some(BitValue::Zero)); // D: 01[0]0
    assert_eq!(iter.next(), Some(BitValue::One)); // D: 0[1]00
    assert_eq!(iter.next(), Some(BitValue::Zero)); // D: [0]100
    assert_eq!(iter.next_primitive::<u8>(), Some(0xBC));
    assert_eq!(iter.next_n(4), Some(bit_string!("x:A")));

    let iter = s.iter().rev();
    assert_eq!(iter.next_n(4), Some(bit_string!("x:A")));
    assert_eq!(iter.next_primitive::<u8>(), Some(0xBC));
    assert_eq!(iter.next(), Some(BitValue::Zero)); // D: [0]100
    assert_eq!(iter.next(), Some(BitValue::One)); // D: 0[1]00
    assert_eq!(iter.next(), Some(BitValue::Zero)); // D: 01[0]0
    assert_eq!(iter.next(), Some(BitValue::Zero)); // D: 010[0]
}

fn allocation() {
    let (msb, lsb): (usize, usize) = bit_string.reserved_space();

    let msb: SetReservedSpace;
    let lsb: SetReservedSpace;
    bit_string.set_reserved_space(msb, lsb); // reserve + shrink_to

    bit_string.shrink_to_fit();
}

fn rotation() {
    let count: usize;
    bit_str.rotate_left(count);
    bit_str.rotate_right(count);
}

/*
    lhs_bit_source can be any BitsSource if rhs_bit_source is a bitstring-like type.
    rhs_bit_source can be any BitsSource if lhs_bit_source is a bitstring-like type.
    A bitstring-like type is any of BitString, &BitString or &BitStr.
 */

fn concatenation() {
    let result: BitString = msb_lhs_bit_source + lsb_rhs_bit_source;

    bit_string.lsb() += bit_source;
}

fn and_or_xor() {
    // All ops for | (OR) and ^ (XOR) also

    let result: BitString = lhs_bit_source & rhs_bit_source;

    // May grow at MSB end
    bit_string &= bit_source;
}

fn not() {
    bit_str.negate();

    let result: BitString = !bit_str;
}

fn eq() {
    let result: bool = lhs_bit_source == rhs_bit_source; // LEXICOGRAPHICAL comparison ("010" != "0010")

    let result: bool = lhs_bit_source.num_eq(rhs_bit_source); // NUMERIC comparison ("010" == "0010")
}

fn ord() {
    let result: Ordering = lhs_bit_source.cmp(rhs_bit_source); // LEXICOGRAPHICAL comparison ("010" > "0011")

    let result: Ordering = lhs_bit_source.num_cmp(rhs_bit_source); // NUMERIC comparison ("010" < "0011")
}

fn shifting() {
    // All ops for >> (SHR) also

    let result: BitString = bit_source << n;

    bit_string_or_str <<= n;
}

impl Hash for BitString {}
impl Hash for BitStr {}

impl Read for &BitStr {}
impl Write for BitString {}
