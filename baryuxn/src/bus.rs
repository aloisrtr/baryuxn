//! # Uxn device bus
//! Uxn interacts with the outside world using devices. These are implementation
//! defined in the form of a trait that satisfies:
//! - reading bytes from addresses 0 to 255
//! - writing bytes from addresses 0 to 255
//!
//! The trait automatically provides methods for writing and reading shorts, but these
//! can be overriden if necessary.

use crate::machine::UxnMachineState;

pub trait UxnDeviceBus {
    // Required methods
    fn read(&mut self, machine: &mut UxnMachineState, address: u8) -> u8;
    fn write(&mut self, machine: &mut UxnMachineState, address: u8, byte: u8);

    // Provided methods
    fn read_short(&mut self, machine: &mut UxnMachineState, address: u8) -> u16 {
        u16::from_be_bytes([
            self.read(machine, address),
            self.read(machine, address.wrapping_add(1)),
        ])
    }
    fn write_short(&mut self, machine: &mut UxnMachineState, address: u8, short: u16) {
        let [msb, lsb] = short.to_be_bytes();
        self.write(machine, address, msb);
        self.write(machine, address.wrapping_add(1), lsb);
    }
}
