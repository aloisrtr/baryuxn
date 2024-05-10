//! # BaryUxn: the baremetal Uxn stack machine
//! An implementation of the [Uxn stack machine](https://wiki.xxiivv.com/site/uxn.html)
//! designed to not rely on `std`.
//!
//! This means it can run on baremetal, and is thoroughly adaptable to any plateform.
//!
//! The source is also designed to be as readable as possible, while compiling
//! down to efficient code regardless of the target plateform.

#![no_std]

use core::ops::{Index, IndexMut};

pub mod bus;
pub mod machine;
pub mod stack;

#[cfg(test)]
mod test;

/// Simple wrapper around an array to represent a Uxn ROM.
#[derive(Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct UxnArrayRom {
    pub data: [u8; 0x10000],
}
impl Default for UxnArrayRom {
    fn default() -> Self {
        Self { data: [0; 0x10000] }
    }
}
impl Index<u16> for UxnArrayRom {
    type Output = u8;
    fn index(&self, index: u16) -> &Self::Output {
        &self.data[index as usize]
    }
}
impl IndexMut<u16> for UxnArrayRom {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        &mut self.data[index as usize]
    }
}
