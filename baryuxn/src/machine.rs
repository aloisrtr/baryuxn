//! # Uxn stack machine
//! Represents a fully functional [Uxn stack-machine](https://wiki.xxiivv.com/site/uxn.html).
//!
//! Execution of code is done using the [`UxnVector`] abstraction. It is an iterator
//! requiring a starting address. It then runs until encountering a `BRK` instruction.
//! Using iterators eases up the interaction. One could easily log instructions
//! executed, for example.
//! ```rust
//! # use baryuxn::machine::*;
//! # let mut machine = UxnMachine(UxnRom([0; 0x10000]), ());
//! for executed_instruction in machine.vector(0x100, &mut devices) {
//!     println!("{executed_instruction}");
//! }
//! ```
//!
//! Stack machines are parametrized by the ROM storage type.
//! This allows for a lot of freedom when it comes to implementation
//! details, for example if you'd need multiple machines to share memory.

use core::ops::{Index, IndexMut};

use crate::{bus::UxnDeviceBus, stack::UxnStack};

/// The Uxn machine, able to execute [Uxntal instructions](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct UxnMachine<T> {
    pub work_stack: UxnStack,
    pub return_stack: UxnStack,

    pub memory: T,
}
impl<T> UxnMachine<T> {
    /// Creates a new [`UxnMachine`] with the given memory contents and empty stacks.
    pub fn new(rom: T) -> Self {
        Self {
            work_stack: UxnStack::default(),
            return_stack: UxnStack::default(),
            memory: rom,
        }
    }
}
impl<T> UxnMachine<T>
where
    T: Index<u16, Output = u8> + IndexMut<u16>,
{
    /// Reads the content of memory at the given address.
    pub fn get_memory(&self, address: u16) -> u8 {
        self.memory[address]
    }
    /// Reads the content of memory at the given address as a short.
    pub fn get_memory_short(&self, address: u16) -> u16 {
        u16::from_be_bytes([self.memory[address], self.memory[address.wrapping_add(1)]])
    }
    /// Returns a mutable reference to the contents of memory at the given address.
    pub fn get_memory_mut(&mut self, address: u16) -> &mut u8 {
        &mut self.memory[address]
    }
    /// Sets a short in memory at the given address.
    pub fn set_memory_short(&mut self, address: u16, value: u16) {
        let [msb, lsb] = value.to_be_bytes();
        self.memory[address] = msb;
        self.memory[address.wrapping_add(1)] = lsb;
    }

    /// Returns a [`UxnVector`] that can be iterated on to execute instructions
    /// until the first `BRK` is encountered.
    pub fn vector<'a, B: UxnDeviceBus<T>>(
        &'a mut self,
        program_counter: u16,
        device_bus: &'a mut B,
    ) -> UxnVector<'_, T, B> {
        UxnVector {
            machine: self,
            program_counter,
            device_bus,
        }
    }

    /// Executes an entire vector of instructions starting at a given program counter.
    pub fn execute_vector<'a, B: UxnDeviceBus<T>>(
        &'a mut self,
        program_counter: u16,
        device_bus: &'a mut B,
    ) {
        UxnVector {
            machine: self,
            program_counter,
            device_bus,
        }
        .for_each(|_instr| {})
    }

    /// Executes a UxnTal operation using modes defined using const generics.
    ///
    /// This allows this crucial function to be monomorphized into 8 mode specific
    /// functions that are optimized individually.
    ///
    /// Returns a value by which the program counter should be offset after executing
    /// said operation.
    pub fn execute_operation<
        const SHORT: bool,
        const RETURN: bool,
        const KEEP: bool,
        B: UxnDeviceBus<T>,
    >(
        &mut self,
        operation: u8,
        mut program_counter: u16,
        device_bus: &mut B,
    ) -> Option<u16> {
        macro_rules! stack {
            () => {
                if RETURN {
                    &mut self.return_stack
                } else {
                    &mut self.work_stack
                }
            };
        }
        macro_rules! return_stack {
            () => {
                if RETURN {
                    &mut self.work_stack
                } else {
                    &mut self.return_stack
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
                        if self.work_stack.pop() != 0 {
                            program_counter =
                                program_counter.wrapping_add(self.get_memory_short(program_counter))
                        }
                        program_counter = program_counter.wrapping_add(2)
                    }
                    (false, true, false) => {
                        // JMI
                        program_counter = program_counter
                            .wrapping_add(self.get_memory_short(program_counter))
                            .wrapping_add(2);
                    }
                    (true, true, false) => {
                        // JSI
                        self.return_stack
                            .push_short(program_counter.wrapping_add(2));
                        program_counter = program_counter
                            .wrapping_add(self.get_memory_short(program_counter))
                            .wrapping_add(2)
                    }
                    (false, _, true) => {
                        // LIT
                        let value = self.get_memory(program_counter);
                        stack!().push(value);
                        program_counter = program_counter.wrapping_add(1);
                    }
                    (true, _, true) => {
                        // LIT2
                        let value = self.get_memory_short(program_counter);
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
                    pop_short::<KEEP>(stack!(), &mut popped)
                        == pop_short::<KEEP>(stack!(), &mut popped)
                } else {
                    pop::<KEEP>(stack!(), &mut popped) == pop::<KEEP>(stack!(), &mut popped)
                } as u8;
                stack!().push(res);
            }
            0x09 => {
                // NEQ
                let res = if SHORT {
                    pop_short::<KEEP>(stack!(), &mut popped)
                        != pop_short::<KEEP>(stack!(), &mut popped)
                } else {
                    pop::<KEEP>(stack!(), &mut popped) != pop::<KEEP>(stack!(), &mut popped)
                } as u8;
                stack!().push(res);
            }
            0x0a => {
                // GTH
                let res = if SHORT {
                    pop_short::<KEEP>(stack!(), &mut popped)
                        < pop_short::<KEEP>(stack!(), &mut popped)
                } else {
                    pop::<KEEP>(stack!(), &mut popped) < pop::<KEEP>(stack!(), &mut popped)
                } as u8;
                stack!().push(res);
            }
            0x0b => {
                // LTH
                let res = if SHORT {
                    pop_short::<KEEP>(stack!(), &mut popped)
                        > pop_short::<KEEP>(stack!(), &mut popped)
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
                    program_counter = program_counter
                        .wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16)
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
                // HACK: we need to explicit RETURN mode here, because the borrow
                // checker can't prove we're not doing bad things otherwise (bad borrow checker, bad)
                // BTW, this should be fine to check because:
                // - if we're borrowing `work_stack!()`, then `stack!()` does not alias `self.return_stack!()`
                // - if we're borrowing `return_stack!()`, then `stack!()` is still ok to use as the first branch shows us
                self.return_stack.push_short(program_counter);
                if SHORT {
                    program_counter = pop_short::<KEEP>(stack!(), &mut popped)
                } else {
                    program_counter = program_counter
                        .wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16)
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
                    let value = self.get_memory_short(address as u16);
                    stack!().push_short(value)
                } else {
                    let value = self.get_memory(address as u16);
                    stack!().push(value)
                }
            }
            0x11 => {
                // STZ
                let address = pop::<KEEP>(stack!(), &mut popped);
                if SHORT {
                    let v = pop_short::<KEEP>(stack!(), &mut popped);
                    self.set_memory_short(address as u16, v)
                } else {
                    let v = pop::<KEEP>(stack!(), &mut popped);
                    *self.get_memory_mut(address as u16) = v
                }
            }
            0x12 => {
                // LDR
                let address = program_counter
                    .wrapping_add_signed((pop::<KEEP>(stack!(), &mut popped) as i8) as i16);
                if SHORT {
                    let value = self.get_memory_short(address as u16);
                    stack!().push_short(value)
                } else {
                    let value = self.get_memory(address as u16);
                    stack!().push(value)
                }
            }
            0x13 => {
                // STR
                let address =
                    program_counter.wrapping_add((pop::<KEEP>(stack!(), &mut popped) as i8) as u16);
                if SHORT {
                    let v = pop_short::<KEEP>(stack!(), &mut popped);
                    self.set_memory_short(address as u16, v)
                } else {
                    let v = pop::<KEEP>(stack!(), &mut popped);
                    *self.get_memory_mut(address as u16) = v
                }
            }
            0x14 => {
                // LDA
                let address = pop_short::<KEEP>(stack!(), &mut popped);
                if SHORT {
                    let value = self.get_memory_short(address as u16);
                    stack!().push_short(value)
                } else {
                    let value = self.get_memory(address as u16);
                    stack!().push(value)
                }
            }
            0x15 => {
                // STA
                let address = pop_short::<KEEP>(stack!(), &mut popped);
                if SHORT {
                    let v = pop_short::<KEEP>(stack!(), &mut popped);
                    self.set_memory_short(address as u16, v);
                } else {
                    let v = pop::<KEEP>(stack!(), &mut popped);
                    *self.get_memory_mut(address as u16) = v
                }
            }
            0x16 => {
                // DEI
                let address = pop::<KEEP>(stack!(), &mut popped);
                if SHORT {
                    let v = device_bus.read_short(self, address);
                    stack!().push_short(v)
                } else {
                    let v = device_bus.read(self, address);
                    stack!().push(v)
                }
            }
            0x17 => {
                // DEO
                let address = pop::<KEEP>(stack!(), &mut popped);
                if SHORT {
                    let value = pop_short::<KEEP>(stack!(), &mut popped);
                    device_bus.write_short(self, address, value);
                } else {
                    let value = pop::<KEEP>(stack!(), &mut popped);
                    device_bus.write(self, address, value);
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
/// on a device, akin to interrupts. To allow for this, vectors can be made unactive
/// by taking their reference to the UxnMachine away for a time.
///
/// # [`FusedIterator`](core::iter::FusedIterator)
/// Note that this cannot implement [`FuserIterator`](core::iter::FusedIterator).
/// Since Uxn does not forbid self modifying code, it is possible to read a `BRK`
/// instruction once, returning `None`, then reading a different instruction at the
/// same location in memory later on.
pub struct UxnVector<'a, T, B> {
    pub machine: &'a mut UxnMachine<T>,
    pub program_counter: u16,
    pub device_bus: &'a mut B,
}
impl<'a, T, B> UxnVector<'a, T, B> {
    /// Makes this [`UxnVector`] into an [`InactiveUxnVector`], leaving another one
    /// to use the machine and devices.
    pub fn make_inactive(self) -> InactiveUxnVector {
        InactiveUxnVector(self.program_counter)
    }
}
impl<'a, T, B> Iterator for UxnVector<'a, T, B>
where
    T: Index<u16, Output = u8> + IndexMut<u16>,
    B: UxnDeviceBus<T>,
{
    type Item = u8;

    /// Steps through the next instruction to execute. Returns `Some(instruction)`
    /// until the executed instruction is `BRK` (`0x00`)
    fn next(&mut self) -> Option<Self::Item> {
        let instruction = self.machine.memory[self.program_counter];
        let operation = instruction & 0x1f;

        // Select the right function to call depending on mode flags
        let program_counter = match instruction & 0xe0 {
            0x00 => self.machine.execute_operation::<false, false, false, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0x20 => self.machine.execute_operation::<true, false, false, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0x40 => self.machine.execute_operation::<false, true, false, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0x60 => self.machine.execute_operation::<true, true, false, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0x80 => self.machine.execute_operation::<false, false, true, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0xa0 => self.machine.execute_operation::<true, false, true, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0xc0 => self.machine.execute_operation::<false, true, false, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            0xe0 => self.machine.execute_operation::<true, true, true, B>(
                operation,
                self.program_counter,
                self.device_bus,
            ),
            _ => unreachable!("You managed to enter a set of modes that does not exist... huh?"),
        };

        if let Some(pc) = program_counter {
            self.program_counter = pc;
            Some(instruction)
        } else {
            None
        }
    }
}

/// Inactive vectors simply store the value of the program counter until they get
/// promoted to the active vector for a [`UxnMachine`].
pub struct InactiveUxnVector(pub u16);
impl InactiveUxnVector {
    /// Promotes this vector to an active [`UxnVector`], allowing it to execute instructions
    /// on a [`UxnMachine`] using the given set of Uxn devices.
    pub fn make_active<'a, T, B>(
        self,
        machine: &'a mut UxnMachine<T>,
        device_bus: &'a mut B,
    ) -> UxnVector<'a, T, B> {
        UxnVector {
            machine,
            program_counter: self.0,
            device_bus,
        }
    }
}
