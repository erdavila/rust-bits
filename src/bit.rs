use crate::bitvalue::BitValue;

pub struct Bit {
    _unsized: [()],
}

impl Bit {
    pub fn read(&self) -> BitValue {
        todo!()
    }

    pub fn write(&mut self, value: BitValue) -> BitValue {
        todo!()
    }

    pub fn modify<F: FnOnce(BitValue) -> BitValue>(&mut self, f: F) {
        todo!()
    }
}
