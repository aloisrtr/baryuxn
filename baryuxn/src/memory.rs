//! # Unx memory trait
//! Needs to be implemented by any object that can be treated as a Uxn memory i.e.
//! take 16bit integers as addresses and return an 8bit unsigned integer.
//!
//! It is automatically implemented for any type that can be indexed by `usize`,
//! such as typical arrays, slices, vectors, etc.

use core::ops::{Index, IndexMut};

pub trait UxnMemory {
    /// Reads the content of memory at the given address.
    fn get_memory(&self, address: u16) -> u8;
    /// Reads the content of memory at the given address as a short.
    fn get_memory_short(&self, address: u16) -> u16 {
        u16::from_be_bytes([
            self.get_memory(address),
            self.get_memory(address.wrapping_add(1)),
        ])
    }
    /// Returns a mutable reference to the contents of memory at the given address.
    fn get_memory_mut(&mut self, address: u16) -> &mut u8;
    /// Sets a short in memory at the given address.
    fn set_memory_short(&mut self, address: u16, value: u16) {
        let [msb, lsb] = value.to_be_bytes();
        *self.get_memory_mut(address) = msb;
        *self.get_memory_mut(address.wrapping_add(1)) = lsb;
    }
}

impl<T: Index<usize, Output = u8> + IndexMut<usize>> UxnMemory for T {
    fn get_memory(&self, address: u16) -> u8 {
        self[address as usize]
    }
    fn get_memory_mut(&mut self, address: u16) -> &mut u8 {
        &mut self[address as usize]
    }
}
