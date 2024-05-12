//! # BaryUxn: the baremetal Uxn stack machine
//! An implementation of the [Uxn stack machine](https://wiki.xxiivv.com/site/uxn.html)
//! designed to not rely on `std`.
//!
//! This means it can run on baremetal, and is thoroughly adaptable to any plateform.
//!
//! The source is also designed to be as readable as possible, while compiling
//! down to efficient code regardless of the target plateform.
//!
//! # STATUS
//! BaryUxn is still in early development, and as such is not thoroughly tested on
//! real world examples. The API may change drastically to ease up implementation.
//!
//! The stack machine itself is well tested, but since the tests rely on baryasm, a
//! UxnTal assembler with the same goals as this crate, some instructions cannot
//! be tested perfectly. It is normal that some tests fail in this early implementation.
//!
//! Put simply, the library is in a usable state, but I would not be surprised that
//! some things are missing.
//!
//! # Quick start
//! To spin up a Uxn emulator, simply load a ROM by opening up a file and loading
//! its byte contents into a form of storage that can be indexed by [`u16`].
//! ```rust
//! # use baryuxn::*;
//! # use baryuxn::machine::*;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     # let rom = UxnArrayRom([0; 0x10000]);
//!     # let mut devices = ();
//!     // Creates a new machine and executes a given ROM, starting at address 0x100.
//!     let mut machine = UxnMachine::new(rom);
//!     machine.execute_vector(0x100, &mut devices);
//! # }
//! ```
//!
//! # Vectors
//! Uxn code is executed using vectors, a continuous stream of Uxn operations ending
//! when it executes the `BRK` instruction.
//!
//! Vectors in BaryUxn are implemented as iterators to allow flexibility. You can then:
//! - log instructions executed
//! - execute a vector step-by-step
//! - or anything fancy like this
//!
//! Creating a [`UxnVector`] is as simple as:
//! ```rust
//! // Creates an execution vector starting at address 0x110 and going until it
//! // executes a BRK instruction.
//! let mut vector = machine.vector(0x110, &mut devices);
//! ```
//! ## Multiple vectors
//! Note that [`UxnVector`] takes ownership through a mutable reference to a [`UxnMachine`]
//! as well as some devices. If you need to keep track of multiple vectors (which
//! can be needed to implement interrupt-like behaviors, like the [Varvara computer](https://wiki.xxiivv.com/site/varvara.html)
//! does), you can use [`InactiveUxnVector`].
//! ```rust
//! let mut vector = machine.vector(0x100, &mut devices);
//! // Do stuff with the original vector...
//! let inactive = vector.make_inactive();
//! let mut second_vector = machine.vector(0x234, &mut devices);
//! // Do stuff with the other vector...
//! second_vector.make_inactive();
//! let mut vector = inactive.make_active(&mut machine, &mut devices);
//! ```
//!
//! # Devices
//! Uxn CPUs can interract with the outside world using devices. To execute instructions,
//! a [`UxnMachine`] requires a mutable reference to a value implementing the [`UxnDeviceBus`]
//! trait.
//!
//! This trait defines two methods: one to read bytes, and another to write them, all
//! addressed by [`u8`]. Writing or reading from a so-called port can trigger specific
//! behavior from your devices, like printing a character to the console or logging some
//! information.
//! ```rust
//! /// Simplified implementation of a CLI Varvara machine.
//! struct CliDeviceBus {
//!     storage: [u8; 0x100],
//!     debug: bool,
//!     should_quit: bool,
//! }
//! impl<T> UxnDeviceBus<T> for CliDeviceBus {
//!     fn read(&mut self, machine: &mut UxnMachine<T>, address: u8) -> u8 {
//!         let page = address & 0xf0;
//!         let port = address & 0x0f;
//!         match page {
//!             0x00 => match port {
//!                 // System
//!                 0x04 => machine.work_stack.pointer,
//!                 0x05 => machine.return_stack.pointer,
//!                 _ => self.storage[address as usize],
//!             },
//!             _ => self.storage[address as usize],
//!         }
//!     }
//!     fn write(&mut self, machine: &mut UxnMachine<T>, address: u8, byte: u8) {
//!         let page = address & 0xf0;
//!         let port = address & 0x0f;
//!         self.storage[address as usize] = byte;
//!         match page {
//!             0x00 => match port {
//!                 // System
//!                 0x04 => machine.work_stack.pointer = byte,
//!                 0x05 => machine.return_stack.pointer = byte,
//!                 0x0e if byte != 0 && self.debug => {
//!                     println!(
//!                         "WST ( {:?} )\nRST ( {:?} )",
//!                         machine.work_stack, machine.return_stack
//!                     );
//!                 }
//!                 0x0f if byte != 0 => self.should_quit = true,
//!                 _ => {}
//!             },
//!             0x10 => match port {
//!                 // Console
//!                 0x08 => print!("{}", byte as char),
//!                 0x09 => eprint!("{}", byte as char),
//!                 _ => {}
//!             },
//!             _ => {}
//!         }
//!     }
//! }
//! ```

#![no_std]

use core::ops::{Index, IndexMut};

mod bus;
pub mod machine;
pub mod stack;

#[cfg(test)]
mod test;

pub use bus::UxnDeviceBus;

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
