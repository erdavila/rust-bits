use crate::bitstr::BitStr;
use crate::bitstring::BitString;
use crate::primitivetype::PrimitiveType;
use crate::BitValue;

pub trait BitSource {}

impl BitSource for BitValue {}
impl BitSource for &BitStr {}
impl BitSource for BitString {}
impl BitSource for &BitString {}
impl<B: PrimitiveType> BitSource for B {}
