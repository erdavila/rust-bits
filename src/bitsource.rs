use crate::bitsprimitive::BitsPrimitive;
use crate::bitstr::BitStr;
use crate::bitstring::BitString;
use crate::BitValue;

pub trait BitSource {}

impl BitSource for BitValue {}
impl BitSource for &BitStr {}
impl BitSource for BitString {}
impl BitSource for &BitString {}
impl<B: BitsPrimitive> BitSource for B {}
