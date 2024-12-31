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
//! ```ignore
//! # use baryuxn::*;
//! # use baryuxn::machine::*;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     # let mut memory = [0; 0x10000];
//!     # let mut devices = ();
//!     // Creates a new machine state (stacks).
//!     let mut machine = UxnMachineState::new();
//!     // Vectors are the main way to execute code, they hold a mutable reference
//!     // to everything needed, and keep running from the starting address until
//!     // a BRK instruction is executed.
//!     UxnVector::new(0x100, &mut machine, &mut memory, &mut devices).execute_till_end();
//! # }
//! ```
//!
//! # Vectors
//! Uxn code is executed using vectors, a continuous stream of Uxn operations ending
//! when it executes the `BRK` instruction.
//!
//! Vectors in BaryUxn are implemented as iterators to allow flexibility. You can then:
//! - log instruction counters
//! - execute a vector step-by-step
//! - or anything you can do with a standard iterator
//!
//! Creating a [`UxnVector`] is as simple as:
//! ```ignore
//! // Creates an execution vector starting at address 0x110 and going until it
//! // executes a BRK instruction.
//! let mut vector = UxnVector(0x110, &mut machine_state, &mut memory, &mut devices);
//! ```
//! ## Multiple vectors
//! Note that [`UxnVector`] takes ownership through a mutable reference to a [`UxnMachine`]
//! as well as memory and devices. If you need to keep track of multiple vectors (which
//! can be needed to implement interrupt-like behaviors, like the [Varvara computer](https://wiki.xxiivv.com/site/varvara.html)
//! does), you can use [`UxnVector::release`]:.
//! ```ignore
//! let mut vector = UxnVector::new(0x100, &mut machine, &mut mem, &mut dev);
//! // Do stuff with the original vector...
//! let next_instruction = vector.release();
//! let mut second_vector = UxnVector::new(0x234, &mut machine, &mut mem, &mut dev);
//! // Do stuff with the other vector...
//! second_vector.release();
//! let mut vector = UxnVector::new(next_instruction, &mut machine, &mut mem, &mut dev);
//! ```
//!
//! # Memory
//! Due to wildly different possible memory implementations (shared memory, parallel access, etc),
//! the implementation for memory components is user-defined. Anything implementing
//! the [`UxnMemory`] trait, which allows you to access the storage using 16 bit
//! integers, works.
//!
//! A blanket implementation for usual arrays, slices, vectors and else is implemented.
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
//! ```ignore
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

pub mod bus;
pub mod machine;
pub mod memory;
pub mod stack;

#[cfg(test)]
mod test;

use bus::UxnDeviceBus;
use machine::UxnMachineState;
use memory::UxnMemory;
use stack::UxnStack;

pub mod prelude {
    pub use crate::bus::UxnDeviceBus;
    pub use crate::machine::UxnMachineState;
    pub use crate::memory::UxnMemory;
    pub use crate::stack::UxnStack;
}

/// An instruction vector, implemented as an iterator that executes instructions
/// in sequence until it encounters a `BRK` instruction.
///
/// Using an iterator for this allows users of the API to execute instructions step
/// by step if they so wish.
///
/// # Queuing vectors
/// The design of some implementations, notably the Varvara ordinator, require
/// their emulator to break evaluation to run a vector when some event happens
/// on a device, akin to interrupts. To allow for this, vectors can release their
/// mutable reference to the UxnMachine, memory and device bus while returning their
/// current program counter to resume progress later.
///
/// # [`FusedIterator`](core::iter::FusedIterator)
/// Note that this cannot implement [`FusedIterator`](core::iter::FusedIterator).
/// Since Uxn does not forbid self modifying code, it is possible to read a `BRK`
/// instruction once, returning `None`, then reading a different instruction at the
/// same location in memory later on.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UxnVector<'a, M, B> {
    pub machine: &'a mut UxnMachineState,
    pub program_counter: u16,
    pub memory: &'a mut M,
    pub device_bus: &'a mut B,
}
impl<'a, M, B> UxnVector<'a, M, B>
where
    M: UxnMemory,
    B: UxnDeviceBus,
{
    /// Creates a new UxnVector starting at the given program counter.
    pub fn new(
        program_counter: u16,
        machine: &'a mut UxnMachineState,
        memory: &'a mut M,
        device_bus: &'a mut B,
    ) -> Self {
        Self {
            machine,
            program_counter,
            memory,
            device_bus,
        }
    }

    /// Executes this vector until it encounters a BRK instruction.
    pub fn execute_till_end(self) {
        self.for_each(|_| {})
    }

    /// Releases the vector, returning its current program counter in order to continue
    /// execution later.
    pub fn release(self) -> u16 {
        self.program_counter
    }
}
impl<M, B> Iterator for UxnVector<'_, M, B>
where
    M: UxnMemory,
    B: UxnDeviceBus,
{
    type Item = (u8, u16);

    /// Steps through the next instruction to execute. Returns `Some((instruction, program_counter))`
    /// until the executed instruction is `BRK` (`0x00`)
    fn next(&mut self) -> Option<Self::Item> {
        let (instruction, next_program_counter) = execute_operation(
            self.machine,
            self.program_counter,
            self.memory,
            self.device_bus,
        );
        if let Some(pc) = next_program_counter {
            let old_pc = self.program_counter;
            self.program_counter = pc;
            Some((instruction, old_pc))
        } else {
            None
        }
    }
}

/// Executes a single UxnTal operation given a program counter, RAM and devices.
///
/// Returns the instruction executed as well as the next value of the program counter after this operation.
pub fn execute_operation<M: UxnMemory, B: UxnDeviceBus>(
    machine_state: &mut UxnMachineState,
    program_counter: u16,
    memory: &mut M,
    device_bus: &mut B,
) -> (u8, Option<u16>) {
    let instruction = memory.get_memory(program_counter);
    let operation = instruction & 0x1f;

    // Select the right function to call depending on mode flags
    (
        instruction,
        match instruction & 0xe0 {
            0x00 => execute_operation_generic::<false, false, false, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0x20 => execute_operation_generic::<true, false, false, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0x40 => execute_operation_generic::<false, true, false, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0x60 => execute_operation_generic::<true, true, false, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0x80 => execute_operation_generic::<false, false, true, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0xa0 => execute_operation_generic::<true, false, true, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0xc0 => execute_operation_generic::<false, true, true, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            0xe0 => execute_operation_generic::<true, true, true, M, B>(
                machine_state,
                operation,
                program_counter,
                memory,
                device_bus,
            ),
            _ => unreachable!("You managed to enter a set of modes that does not exist... huh?"),
        },
    )
}

/// Executes a UxnTal operation using modes defined using const generics.
///
/// This allows this crucial function to be monomorphized into 8 mode specific
/// functions that are optimized individually.
///
/// Returns the next value of the program counter after this operation.
fn execute_operation_generic<
    const SHORT: bool,
    const RETURN: bool,
    const KEEP: bool,
    M: UxnMemory,
    B: UxnDeviceBus,
>(
    machine_state: &mut UxnMachineState,
    operation: u8,
    mut program_counter: u16,
    memory: &mut M,
    device_bus: &mut B,
) -> Option<u16> {
    macro_rules! stack {
        () => {
            if RETURN {
                &mut machine_state.return_stack
            } else {
                &mut machine_state.work_stack
            }
        };
    }
    macro_rules! return_stack {
        () => {
            if RETURN {
                &mut machine_state.work_stack
            } else {
                &mut machine_state.return_stack
            }
        };
    }

    let mut popped = 0;
    fn pop<const KEEP: bool>(stack: &mut UxnStack, popped: &mut i8) -> u8 {
        if KEEP {
            *popped -= 1;
            stack.get(*popped + 1)
        } else {
            stack.pop()
        }
    }
    fn pop_short<const KEEP: bool>(stack: &mut UxnStack, popped: &mut i8) -> u16 {
        if KEEP {
            *popped -= 2;
            stack.get_short(*popped + 2)
        } else {
            stack.pop_short()
        }
    }

    program_counter = program_counter.wrapping_add(1);
    match operation {
        0x00 => {
            // Immediate opcodes depend simply on which modes are set.
            match (SHORT, RETURN, KEEP) {
                (false, false, false) => return None, // BRK
                (true, false, false) => {
                    // JCI
                    if machine_state.work_stack.pop() != 0 {
                        program_counter =
                            program_counter.wrapping_add(memory.get_memory_short(program_counter))
                    }
                    program_counter = program_counter.wrapping_add(2)
                }
                (false, true, false) => {
                    // JMI
                    program_counter = program_counter
                        .wrapping_add(memory.get_memory_short(program_counter))
                        .wrapping_add(2);
                }
                (true, true, false) => {
                    // JSI
                    machine_state
                        .return_stack
                        .push_short(program_counter.wrapping_add(2));
                    program_counter = program_counter
                        .wrapping_add(memory.get_memory_short(program_counter))
                        .wrapping_add(2)
                }
                (false, _, true) => {
                    // LIT
                    let value = memory.get_memory(program_counter);
                    stack!().push(value);
                    program_counter = program_counter.wrapping_add(1);
                }
                (true, _, true) => {
                    // LIT2
                    let value = memory.get_memory_short(program_counter);
                    stack!().push_short(value);
                    program_counter = program_counter.wrapping_add(2)
                }
            }
        }

        // General opcodes
        0x01 => {
            // INC
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped).wrapping_add(1);
                stack!().push_short(v)
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped).wrapping_add(1);
                stack!().push(v)
            }
        }
        0x02 => {
            // POP
            if SHORT {
                pop_short::<KEEP>(stack!(), &mut popped);
            } else {
                pop::<KEEP>(stack!(), &mut popped);
            }
        }
        0x03 => {
            // NIP
            if SHORT {
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                let _ = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(b);
            } else {
                let b = pop::<KEEP>(stack!(), &mut popped);
                let _ = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(b);
            }
        }
        0x04 => {
            // SWP
            if SHORT {
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(b);
                stack!().push_short(a);
            } else {
                let b = pop::<KEEP>(stack!(), &mut popped);
                let a = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(b);
                stack!().push(a);
            }
        }
        0x05 => {
            // ROT
            if SHORT {
                let c = pop_short::<KEEP>(stack!(), &mut popped);
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(b);
                stack!().push_short(c);
                stack!().push_short(a);
            } else {
                let c = pop::<KEEP>(stack!(), &mut popped);
                let b = pop::<KEEP>(stack!(), &mut popped);
                let a = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(b);
                stack!().push(c);
                stack!().push(a);
            }
        }
        0x06 => {
            // DUP
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(v);
                stack!().push_short(v);
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(v);
                stack!().push(v);
            }
        }
        0x07 => {
            // OVR
            if SHORT {
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a);
                stack!().push_short(b);
                stack!().push_short(a);
            } else {
                let b = pop::<KEEP>(stack!(), &mut popped);
                let a = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a);
                stack!().push(b);
                stack!().push(a);
            }
        }
        0x08 => {
            // EQU
            let res = if SHORT {
                pop_short::<KEEP>(stack!(), &mut popped) == pop_short::<KEEP>(stack!(), &mut popped)
            } else {
                pop::<KEEP>(stack!(), &mut popped) == pop::<KEEP>(stack!(), &mut popped)
            } as u8;
            stack!().push(res);
        }
        0x09 => {
            // NEQ
            let res = if SHORT {
                pop_short::<KEEP>(stack!(), &mut popped) != pop_short::<KEEP>(stack!(), &mut popped)
            } else {
                pop::<KEEP>(stack!(), &mut popped) != pop::<KEEP>(stack!(), &mut popped)
            } as u8;
            stack!().push(res);
        }
        0x0a => {
            // GTH
            let res = if SHORT {
                pop_short::<KEEP>(stack!(), &mut popped) < pop_short::<KEEP>(stack!(), &mut popped)
            } else {
                pop::<KEEP>(stack!(), &mut popped) < pop::<KEEP>(stack!(), &mut popped)
            } as u8;
            stack!().push(res);
        }
        0x0b => {
            // LTH
            let res = if SHORT {
                pop_short::<KEEP>(stack!(), &mut popped) > pop_short::<KEEP>(stack!(), &mut popped)
            } else {
                pop::<KEEP>(stack!(), &mut popped) > pop::<KEEP>(stack!(), &mut popped)
            } as u8;
            stack!().push(res);
        }
        0x0c => {
            // JMP
            if SHORT {
                program_counter = pop_short::<KEEP>(stack!(), &mut popped)
            } else {
                program_counter =
                    program_counter.wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16)
            }
        }
        0x0d => {
            // JCN
            if pop::<KEEP>(stack!(), &mut popped) != 0 {
                if SHORT {
                    program_counter = pop_short::<KEEP>(stack!(), &mut popped)
                } else {
                    program_counter = program_counter
                        .wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16)
                }
            }
        }
        0x0e => {
            // JSR
            machine_state.return_stack.push_short(program_counter);
            if SHORT {
                program_counter = pop_short::<KEEP>(stack!(), &mut popped)
            } else {
                program_counter =
                    program_counter.wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16)
            }
        }
        0x0f => {
            // STH
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped);
                return_stack!().push_short(v);
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped);
                return_stack!().push(v);
            }
        }
        0x10 => {
            // LDZ
            let address = pop::<KEEP>(stack!(), &mut popped);
            if SHORT {
                let value = memory.get_memory_short(address as u16);
                stack!().push_short(value)
            } else {
                let value = memory.get_memory(address as u16);
                stack!().push(value)
            }
        }
        0x11 => {
            // STZ
            let address = pop::<KEEP>(stack!(), &mut popped);
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped);
                memory.set_memory_short(address as u16, v)
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped);
                *memory.get_memory_mut(address as u16) = v
            }
        }
        0x12 => {
            // LDR
            let address = program_counter
                .wrapping_add_signed((pop::<KEEP>(stack!(), &mut popped) as i8) as i16);
            if SHORT {
                let value = memory.get_memory_short(address as u16);
                stack!().push_short(value)
            } else {
                let value = memory.get_memory(address as u16);
                stack!().push(value)
            }
        }
        0x13 => {
            // STR
            let address =
                program_counter.wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16);
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped);
                memory.set_memory_short(address as u16, v)
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped);
                *memory.get_memory_mut(address as u16) = v
            }
        }
        0x14 => {
            // LDA
            let address = pop_short::<KEEP>(stack!(), &mut popped);
            if SHORT {
                let value = memory.get_memory_short(address);
                stack!().push_short(value)
            } else {
                let value = memory.get_memory(address);
                stack!().push(value)
            }
        }
        0x15 => {
            // STA
            let address = pop_short::<KEEP>(stack!(), &mut popped);
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped);
                memory.set_memory_short(address, v);
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped);
                *memory.get_memory_mut(address) = v
            }
        }
        0x16 => {
            // DEI
            let address = pop::<KEEP>(stack!(), &mut popped);
            if SHORT {
                let v = device_bus.read_short(machine_state, address);
                stack!().push_short(v)
            } else {
                let v = device_bus.read(machine_state, address);
                stack!().push(v)
            }
        }
        0x17 => {
            // DEO
            let address = pop::<KEEP>(stack!(), &mut popped);
            if SHORT {
                let value = pop_short::<KEEP>(stack!(), &mut popped);
                device_bus.write_short(machine_state, address, value);
            } else {
                let value = pop::<KEEP>(stack!(), &mut popped);
                device_bus.write(machine_state, address, value);
            }
        }
        0x18 => {
            // ADD
            if SHORT {
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a.wrapping_add(b));
            } else {
                let a = pop::<KEEP>(stack!(), &mut popped);
                let b = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a.wrapping_add(b));
            }
        }
        0x19 => {
            // SUB
            if SHORT {
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a.wrapping_sub(b));
            } else {
                let b = pop::<KEEP>(stack!(), &mut popped);
                let a = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a.wrapping_sub(b));
            }
        }
        0x1a => {
            // MUL
            if SHORT {
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a.wrapping_mul(b));
            } else {
                let a = pop::<KEEP>(stack!(), &mut popped);
                let b = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a.wrapping_mul(b));
            }
        }
        0x1b => {
            // DIV
            if SHORT {
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                if b == 0 {
                    stack!().push_short(0)
                } else {
                    stack!().push_short(a.wrapping_div(b));
                }
            } else {
                let b = pop::<KEEP>(stack!(), &mut popped);
                let a = pop::<KEEP>(stack!(), &mut popped);
                if b == 0 {
                    stack!().push(0)
                } else {
                    stack!().push(a.wrapping_div(b));
                }
            }
        }
        0x1c => {
            // AND
            if SHORT {
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a & b);
            } else {
                let a = pop::<KEEP>(stack!(), &mut popped);
                let b = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a & b);
            }
        }
        0x1d => {
            // ORA
            if SHORT {
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a | b);
            } else {
                let a = pop::<KEEP>(stack!(), &mut popped);
                let b = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a | b);
            }
        }
        0x1e => {
            // EOR
            if SHORT {
                let a = pop_short::<KEEP>(stack!(), &mut popped);
                let b = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short(a ^ b);
            } else {
                let a = pop::<KEEP>(stack!(), &mut popped);
                let b = pop::<KEEP>(stack!(), &mut popped);
                stack!().push(a ^ b);
            }
        }
        0x1f => {
            // SFT
            let shift = pop::<KEEP>(stack!(), &mut popped);
            let shift_right = 0x0f & shift;
            let shift_left = (0xf0 & shift) >> 4;
            if SHORT {
                let v = pop_short::<KEEP>(stack!(), &mut popped);
                stack!().push_short((v >> shift_right) << shift_left)
            } else {
                let v = pop::<KEEP>(stack!(), &mut popped);
                stack!().push((v >> shift_right) << shift_left)
            }
        }
        _ => {}
    }

    Some(program_counter)
}
