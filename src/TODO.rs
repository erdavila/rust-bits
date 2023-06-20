impl BitsSource for BitValue {}
impl BitsSource for BitString {}
impl BitsSource for &BitString {}
impl BitsSource for &BitStr {}
impl BitsSource for u8 {} // also for u16, u32, u64, u128, usize
impl<B> BitsSource for [B] where B: BitsSource {}
impl<B, const N: usize> BitsSource for [B; N] where B: BitsSource {} // ?
impl<B> BitsSource for &[B] where B: BitsSource {} // ?
impl<B, const N: usize> BitsSource for &[B; N] where B: BitsSource {} // ?

fn bit_string_construction() {
    BitString::new();
    BitString::default();
    Default::default();

    bit_string!("1001011");
    bit_string!("b:1001011");
    bit_string!("x:abe03da");
    bit_string!("x:abe_03d");
    bit_string!("x:abe03da", u8);

    let msb: usize;
    let lsb: usize;
    BitString::with_reserved_space(msb, lsb);

    let bit: BitValue;
    let len: usize;
    BitString::repeat(bit, len);

    fn source() -> impl BitsSource;
    BitString::from(source());

    fn source<const N: usize>() -> [impl BitsSource; N];
    BitString::from(source());

    fn source() -> &[impl BitsSource];
    BitString::from(source());

    fn iter<B: BitsSource>() -> impl IntoIterator<Item = B>;
    fn iter<B: BitsSource>() -> impl IntoIterator<Item = &B>;
    BitString::from_iter(iter());

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

    // Also for mut!
    let bit: &Bit;
    let bit_str: &BitStr = bit.as_bit_str();
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

    let (lsb, msb): (&BitStr, &BitStr) = bit_str.split_at(index);

    let (lsb, msb): (&mut BitStr, &mut BitStr) = bit_str.split_at_mut(index);

    let b: bool = bit_str.lsb().matches(source()); // like {starts,ends}_with()
}

fn adding() {
    fn source() -> impl BitsSource;
    let index: usize;
    bit_string.insert(index, source());

    fn source() -> impl BitsSource;
    bit_string.lsb_mut().push(source());
}

fn removing() {
    let index: usize;
    let begin: usize;
    let end: usize;
    let removed: Option<BitValue> = bit_string.remove(index);
    let removed: Option<u8> = bit_string.remove(index); // ... and other primitive types
    let removed: Option<BitString> = bit_string.remove_n(begin..end);

    let count: usize;
    let popped: Option<BitValue> = bit_string.lsb_mut().pop::<BitValue>();
    let popped: Option<u8> = bit_string.lsb_mut().pop::<u8>(); // ... and other primitive types
    let popped: Option<BitString> = bit_string.lsb_mut().pop_n(count);
    let popped: BitString = bit_string.lsb_mut().pop_up_to(count);

    let bit: BitValue;
    let count: usize = bit_string.lsb_mut().strip(bit);

    let count: usize;
    bit_string.lsb_mut().discard(count);

    let len: usize;
    bit_string.lsb_mut().truncate(len);

    bit_string.clear();
}

fn adding_or_removing() {
    let bit: BitValue;
    let new_len: usize;
    bit_string.lsb_mut().resize(new_len, bit);
    assert_eq!(bs.len(), new_len);

    fn source() -> impl BitsSource;
    let removed: BitString = bit_string.splice(range, source());
    let removed: Option<BitString> = bit_str.replace(range, source()); // source must have same number of bits

    bit_str.fill(bit);
}

trait BitIterator<B, PII: PrimitiveIterItem, S>: Iterator<Item = B> + DoubleEndedIterator + ExactSizeIterator + FusedIterator {
    fn next_primitive<P: BitsPrimitive>(&mut self) -> Option<PII::Item<P>>;
    fn next_n(&mut self, len: usize) -> Option<S>;
    fn rev(self) -> impl BitIterator<B, P, S>;
    fn primitives<P: BitsPrimitive>(self) -> impl BitBlockIterator<PII::Item<P>, S>;
    fn substrings(self, len: usize) -> impl BitBlockIterator<S, S>;
}

trait PrimitiveIterItem {
    type Item<P: BitsPrimitive>;
}

struct PrimitiveCopy;
impl PrimitiveIterItem for PrimitiveCopy {
    type Item<P: BitsPrimitive> = P;
}

struct PrimitiveRef;
impl PrimitiveIterItem for PrimitiveRef {
    type Item<P: BitsPrimitive> = &Primitive<P>;
}

struct PrimitiveMut;
impl PrimitiveIterItem for PrimitiveMut {
    type Item<P: BitsPrimitive> = &mut Primitive<P>;
}

struct Iter {}
impl BitIterator<BitValue, PrimitiveCopy, &BitStr> for Iter {}

struct IterRef {}
impl BitIterator<&Bit, PrimitiveRef, &BitStr> for IterRef {}

struct IterMut {}
impl BitIterator<&mut Bit, PrimitiveMut, &mut BitStr> for IterMut {}

fn iteration() {
    let iter: Iter = bit_str.iter();
    let iter: IterRef = bit_str.iter_ref();
    let iter: IterMut = bit_str.iter_mut();
}

struct IntoIter {}
impl BitIterator<BitValue, PrimitiveCopy, BitString> for IntoIter {}

fn consumption() {
    let iter: impl IntoIter = bit_string.into_iter();
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

fn substrings_iteration() {
    let iter = bit_str.iter().substrings(3);
    let _: Option<&BitStr> = iter.next();
    let _: Option<&BitStr> = iter.into_remainder();

    let iter = bit_str.iter_ref().substrings(3);
    let _: Option<&BitStr> = iter.next();
    let _: Option<&BitStr> = iter.into_remainder();

    let iter = bit_str.iter_mut().substrings(3);
    let _: Option<&mut BitStr> = iter.next();
    let _: Option<&mut BitStr> = iter.into_remainder();

    let iter = bit_str.into_iter().substrings(3);
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

fn concatenation() {
    let result: BitString = msb_bit_source + lsb_bit_source;

    bit_string.lsb_mut() += bit_source;
}

fn and_or_xor() {
    // All ops for | (OR) and ^ (XOR) also

    let result: BitString = bit_source_1 & bit_source_2;

    // May grow at MSB end
    bit_string &= bit_source;
}

fn not() {
    bit_str.negate();

    let result: BitString = !bit_str;
}

fn eq() {
    let result: bool = bit_source_1 == bit_source_2; // LEXICOGRAPHICAL comparison ("010" != "0010")

    let result: bool = bit_source_1.num_eq(bit_source_2); // NUMERIC comparison - ("010" == "0010")
}

fn ord() {
    let result: Ordering = bit_source_1.cmp(bit_source_2); // LEXICOGRAPHICAL comparison ("010" > "0011")

    let result: Ordering = bit_source_1.num_cmp(bit_source_2); // NUMERIC comparison - ("010" < "0011")
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
