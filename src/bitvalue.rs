#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u8)]
pub enum BitValue {
    Zero,
    One,
}

impl BitValue {
    pub fn to_bool(self) -> bool {
        match self {
            BitValue::Zero => false,
            BitValue::One => true,
        }
    }
}

impl From<bool> for BitValue {
    fn from(value: bool) -> Self {
        match value {
            true => Self::One,
            false => Self::Zero,
        }
    }
}
