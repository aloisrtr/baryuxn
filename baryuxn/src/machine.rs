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
//! for executed_instruction in machine.vector(0x100) {
//!     println!("{executed_instruction}");
//! }
//! ```
//!
//! Stack machines are parametrized by the ROM storage type ([`T`]) and a type implementing
//! [`UxnDeviceBus`] ([`B`]). This allows for a lot of freedom when it comes to implementation
//! details.

use core::ops::{Index, IndexMut};

use crate::{bus::UxnDeviceBus, stack::UxnStack};
/// The Uxn machine, able to execute [Uxntal instructions](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
pub struct UxnMachine<T, B> {
    work_stack: UxnStack,
    return_stack: UxnStack,

    memory: T,
    device_bus: B,
}
impl<T, B> UxnMachine<T, B>
where
    T: Index<u16, Output = u8> + IndexMut<u16>,
    B: UxnDeviceBus,
{
    pub fn new(rom: T, device_bus: B) -> Self {
        Self {
            work_stack: UxnStack::default(),
            return_stack: UxnStack::default(),
            memory: rom,
            device_bus,
        }
    }

    pub fn work_stack(&self) -> &UxnStack {
        &self.work_stack
    }
    pub fn return_stack(&self) -> &UxnStack {
        &self.return_stack
    }

    pub fn read_memory(&self, address: u16) -> u8 {
        Self::get_memory(&self.memory, address)
    }
    pub fn read_memory_short(&self, address: u16) -> u16 {
        Self::get_memory_short(&self.memory, address)
    }
    pub fn memory(&self) -> &T {
        &self.memory
    }

    /// Reads a byte from the machine's memory.
    fn get_memory(memory: &T, address: u16) -> u8 {
        memory[address]
    }

    /// Gets a mutable reference to a byte in the machine's memory.
    fn get_memory_mut(memory: &mut T, address: u16) -> &mut u8 {
        &mut memory[address]
    }

    /// Reads a short from the machine's memory.
    fn get_memory_short(memory: &T, address: u16) -> u16 {
        u16::from_be_bytes([memory[address], memory[address.wrapping_add(1)]])
    }

    /// Gets a mutable reference to a short in the machine's memory.
    fn set_memory_short_mut(memory: &mut T, address: u16, value: u16) {
        let [msb, lsb] = value.to_be_bytes();
        memory[address] = msb;
        memory[address.wrapping_add(1)] = lsb;
    }

    /// Returns a [`UxnVector`] that can be iterated on to execute instructions
    /// until the first `BRK` is encountered.
    pub fn vector(&mut self, program_counter: u16) -> UxnVector<'_, T, B> {
        UxnVector {
            machine: self,
            program_counter,
        }
    }

    /// Executes an entire vector of instructions starting at a given program counter.
    pub fn execute_vector(&mut self, program_counter: u16) {
        UxnVector {
            machine: self,
            program_counter,
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
    pub fn execute_operation<const SHORT: bool, const RETURN: bool, const KEEP: bool>(
        &mut self,
        operation: u8,
        program_counter: u16,
    ) -> Option<u16> {
        let stack = if RETURN {
            &mut self.return_stack
        } else {
            &mut self.work_stack
        };

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

        match operation {
            0x00 => {
                // Immediate opcodes depend simply on which modes are set.
                match (SHORT, RETURN, KEEP) {
                    (false, false, false) => return None, // BRK
                    (true, false, false) => {
                        // JCI
                        return Some(if self.work_stack.pop() == 0 {
                            Self::get_memory_short(&self.memory, program_counter.wrapping_add(1))
                        } else {
                            2
                        });
                    }
                    (false, true, false) => {
                        return Some(Self::get_memory_short(
                            &self.memory,
                            program_counter.wrapping_add(1),
                        ))
                    } // JMI
                    (true, true, false) => {
                        // JSI
                        self.return_stack
                            .push_short(program_counter.wrapping_add(2));
                        return Some(Self::get_memory_short(
                            &self.memory,
                            program_counter.wrapping_add(1),
                        ));
                    }
                    (false, _, true) => {
                        // LIT
                        stack.push(Self::get_memory(
                            &self.memory,
                            program_counter.wrapping_add(1),
                        ));
                        return Some(2);
                    }
                    (true, _, true) => {
                        // LIT2
                        stack.push_short(Self::get_memory_short(
                            &self.memory,
                            program_counter.wrapping_add(1),
                        ));
                        return Some(3);
                    }
                }
            }

            // General opcodes
            0x01 => {
                // INC
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped).wrapping_add(1);
                    stack.push_short(v)
                } else {
                    let v = pop::<KEEP>(stack, &mut popped).wrapping_add(1);
                    stack.push(v)
                }
            }
            0x02 => {
                // POP
                if SHORT {
                    pop_short::<KEEP>(stack, &mut popped);
                } else {
                    pop::<KEEP>(stack, &mut popped);
                }
            }
            0x03 => {
                // NIP
                if SHORT {
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    let _ = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(b);
                } else {
                    let b = pop::<KEEP>(stack, &mut popped);
                    let _ = pop::<KEEP>(stack, &mut popped);
                    stack.push(b);
                }
            }
            0x04 => {
                // SWP
                if SHORT {
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(b);
                    stack.push_short(a);
                } else {
                    let b = pop::<KEEP>(stack, &mut popped);
                    let a = pop::<KEEP>(stack, &mut popped);
                    stack.push(b);
                    stack.push(a);
                }
            }
            0x05 => {
                // ROT
                if SHORT {
                    let c = pop_short::<KEEP>(stack, &mut popped);
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(b);
                    stack.push_short(c);
                    stack.push_short(a);
                } else {
                    let c = pop::<KEEP>(stack, &mut popped);
                    let b = pop::<KEEP>(stack, &mut popped);
                    let a = pop::<KEEP>(stack, &mut popped);
                    stack.push(b);
                    stack.push(c);
                    stack.push(a);
                }
            }
            0x06 => {
                // DUP
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(v);
                    stack.push_short(v);
                } else {
                    let v = pop::<KEEP>(stack, &mut popped);
                    stack.push(v);
                    stack.push(v);
                }
            }
            0x07 => {
                // OVR
                if SHORT {
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a);
                    stack.push_short(b);
                    stack.push_short(a);
                } else {
                    let b = pop::<KEEP>(stack, &mut popped);
                    let a = pop::<KEEP>(stack, &mut popped);
                    stack.push(a);
                    stack.push(b);
                    stack.push(a);
                }
            }
            0x08 => {
                // EQU
                let res = if SHORT {
                    pop_short::<KEEP>(stack, &mut popped) == pop_short::<KEEP>(stack, &mut popped)
                } else {
                    pop::<KEEP>(stack, &mut popped) == pop::<KEEP>(stack, &mut popped)
                } as u8;
                stack.push(res);
            }
            0x09 => {
                // NEQ
                let res = if SHORT {
                    pop_short::<KEEP>(stack, &mut popped) != pop_short::<KEEP>(stack, &mut popped)
                } else {
                    pop::<KEEP>(stack, &mut popped) != pop::<KEEP>(stack, &mut popped)
                } as u8;
                stack.push(res);
            }
            0x0a => {
                // GTH
                let res = if SHORT {
                    pop_short::<KEEP>(stack, &mut popped) < pop_short::<KEEP>(stack, &mut popped)
                } else {
                    pop::<KEEP>(stack, &mut popped) < pop::<KEEP>(stack, &mut popped)
                } as u8;
                stack.push(res);
            }
            0x0b => {
                // LTH
                let res = if SHORT {
                    pop_short::<KEEP>(stack, &mut popped) > pop_short::<KEEP>(stack, &mut popped)
                } else {
                    pop::<KEEP>(stack, &mut popped) > pop::<KEEP>(stack, &mut popped)
                } as u8;
                stack.push(res);
            }
            0x0c => {
                // JMP
                return Some(if SHORT {
                    pop_short::<KEEP>(stack, &mut popped).wrapping_sub(program_counter)
                } else {
                    program_counter.wrapping_add((pop::<KEEP>(stack, &mut popped) as i8) as u16)
                });
            }
            0x0d => {
                // JCN
                if pop::<KEEP>(stack, &mut popped) != 0 {
                    return Some(if SHORT {
                        pop_short::<KEEP>(stack, &mut popped).wrapping_sub(program_counter)
                    } else {
                        program_counter.wrapping_add((pop::<KEEP>(stack, &mut popped) as i8) as u16)
                    });
                }
            }
            0x0e => {
                // JSR
                // HACK: we need to explicit RETURN mode here, because the borrow
                // checker can't prove we're not doing bad things otherwise (bad borrow checker, bad)
                // BTW, this should be fine to check because:
                // - if we're borrowing `work_stack`, then `stack` does not alias `self.return_stack`
                // - if we're borrowing `return_stack`, then `stack` is still ok to use as the first branch shows us
                if RETURN {
                    stack.push_short(program_counter);
                    return Some(if SHORT {
                        pop_short::<KEEP>(stack, &mut popped).wrapping_sub(program_counter)
                    } else {
                        program_counter.wrapping_add((pop::<KEEP>(stack, &mut popped) as i8) as u16)
                    });
                } else {
                    self.return_stack.push_short(program_counter);
                    return Some(if SHORT {
                        pop_short::<KEEP>(&mut self.work_stack, &mut popped)
                            .wrapping_sub(program_counter)
                    } else {
                        program_counter.wrapping_add(
                            (pop::<KEEP>(&mut self.work_stack, &mut popped) as i8) as u16,
                        )
                    });
                };
            }
            0x0f => {
                // STH
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped);
                    if RETURN {
                        self.work_stack.push_short(v)
                    } else {
                        self.return_stack.push_short(v)
                    }
                } else {
                    let v = pop::<KEEP>(stack, &mut popped);
                    if RETURN {
                        self.work_stack.push(v)
                    } else {
                        self.return_stack.push(v)
                    }
                }
            }
            0x10 => {
                // LDZ
                let address = pop::<KEEP>(stack, &mut popped);
                if SHORT {
                    stack.push_short(Self::get_memory_short(&self.memory, address as u16))
                } else {
                    stack.push(Self::get_memory(&self.memory, address as u16))
                }
            }
            0x11 => {
                // STZ
                let address = pop::<KEEP>(stack, &mut popped);
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped);
                    Self::set_memory_short_mut(&mut self.memory, address as u16, v)
                } else {
                    let v = pop::<KEEP>(stack, &mut popped);
                    *Self::get_memory_mut(&mut self.memory, address as u16) = v
                }
            }
            0x12 => {
                // LDR
                let address = program_counter
                    .wrapping_add_signed((pop::<KEEP>(stack, &mut popped) as i8) as i16);
                if SHORT {
                    stack.push_short(Self::get_memory_short(&self.memory, address as u16))
                } else {
                    stack.push(Self::get_memory(&self.memory, address as u16))
                }
            }
            0x13 => {
                // STR
                let address =
                    program_counter.wrapping_add((pop::<KEEP>(stack, &mut popped) as i8) as u16);
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped);
                    Self::set_memory_short_mut(&mut self.memory, address as u16, v)
                } else {
                    let v = pop::<KEEP>(stack, &mut popped);
                    *Self::get_memory_mut(&mut self.memory, address as u16) = v
                }
            }
            0x14 => {
                // LDA
                let address = pop_short::<KEEP>(stack, &mut popped);
                if SHORT {
                    stack.push_short(Self::get_memory_short(&self.memory, address as u16))
                } else {
                    stack.push(Self::get_memory(&self.memory, address as u16))
                }
            }
            0x15 => {
                // STA
                let address = pop_short::<KEEP>(stack, &mut popped);
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped);
                    Self::set_memory_short_mut(&mut self.memory, address as u16, v)
                } else {
                    let v = pop::<KEEP>(stack, &mut popped);
                    *Self::get_memory_mut(&mut self.memory, address as u16) = v
                }
            }
            0x16 => {
                // DEI
                let address = pop::<KEEP>(stack, &mut popped);
                if SHORT {
                    stack.push_short(self.device_bus.read_short(address))
                } else {
                    stack.push(self.device_bus.read(address))
                }
            }
            0x17 => {
                // DEO
                let address = pop::<KEEP>(stack, &mut popped);
                if SHORT {
                    let value = pop_short::<KEEP>(stack, &mut popped);
                    self.device_bus.write_short(address, value);
                } else {
                    let value = pop::<KEEP>(stack, &mut popped);
                    self.device_bus.write(address, value);
                }
            }
            0x18 => {
                // ADD
                if SHORT {
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a.wrapping_add(b));
                } else {
                    let a = pop::<KEEP>(stack, &mut popped);
                    let b = pop::<KEEP>(stack, &mut popped);
                    stack.push(a.wrapping_add(b));
                }
            }
            0x19 => {
                // SUB
                if SHORT {
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a.wrapping_sub(b));
                } else {
                    let b = pop::<KEEP>(stack, &mut popped);
                    let a = pop::<KEEP>(stack, &mut popped);
                    stack.push(a.wrapping_sub(b));
                }
            }
            0x1a => {
                // MUL
                if SHORT {
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a.wrapping_mul(b));
                } else {
                    let a = pop::<KEEP>(stack, &mut popped);
                    let b = pop::<KEEP>(stack, &mut popped);
                    stack.push(a.wrapping_mul(b));
                }
            }
            0x1b => {
                // DIV
                if SHORT {
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    if b == 0 {
                        stack.push_short(0)
                    } else {
                        stack.push_short(a.wrapping_div(b));
                    }
                } else {
                    let b = pop::<KEEP>(stack, &mut popped);
                    let a = pop::<KEEP>(stack, &mut popped);
                    if b == 0 {
                        stack.push(0)
                    } else {
                        stack.push(a.wrapping_div(b));
                    }
                }
            }
            0x1c => {
                // AND
                if SHORT {
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a & b);
                } else {
                    let a = pop::<KEEP>(stack, &mut popped);
                    let b = pop::<KEEP>(stack, &mut popped);
                    stack.push(a & b);
                }
            }
            0x1d => {
                // ORA
                if SHORT {
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a | b);
                } else {
                    let a = pop::<KEEP>(stack, &mut popped);
                    let b = pop::<KEEP>(stack, &mut popped);
                    stack.push(a | b);
                }
            }
            0x1e => {
                // EOR
                if SHORT {
                    let a = pop_short::<KEEP>(stack, &mut popped);
                    let b = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short(a ^ b);
                } else {
                    let a = pop::<KEEP>(stack, &mut popped);
                    let b = pop::<KEEP>(stack, &mut popped);
                    stack.push(a ^ b);
                }
            }
            0x1f => {
                // SFT
                let shift = pop::<KEEP>(stack, &mut popped);
                let shift_right = 0x0f & shift;
                let shift_left = (0xf0 & shift) >> 4;
                if SHORT {
                    let v = pop_short::<KEEP>(stack, &mut popped);
                    stack.push_short((v >> shift_right) << shift_left)
                } else {
                    let v = pop::<KEEP>(stack, &mut popped);
                    stack.push((v >> shift_right) << shift_left)
                }
            }
            _ => {}
        }

        Some(1)
    }
}

/// An instruction vector, implemented as an iterator that executes instructions
/// in sequence until it encounters a `BRK` instruction.
///
/// Using an iterator for this allows users of the API to execute instructions step
/// by step if they so wish.
///
/// # [`FusedIterator`](core::iter::FusedIterator)
/// Note that this cannot implement [`FuserIterator`](core::iter::FusedIterator).
/// Since Uxn does not forbid self modifying code, it is possible to read a `BRK`
/// instruction once, returning `None`, then reading a different instruction at the
/// same location in memory later on.
pub struct UxnVector<'a, T, B> {
    pub(crate) machine: &'a mut UxnMachine<T, B>,
    pub(crate) program_counter: u16,
}
impl<'a, T, B> Iterator for UxnVector<'a, T, B>
where
    T: Index<u16, Output = u8> + IndexMut<u16>,
    B: UxnDeviceBus,
{
    type Item = u8;

    /// Steps through the next instruction to execute. Returns `Some(instruction)`
    /// until the executed instruction is `BRK` (`0x00`)
    fn next(&mut self) -> Option<Self::Item> {
        let instruction = self.machine.memory[self.program_counter];
        let operation = instruction & 0x1f;

        // Select the right function to call depending on mode flags
        let program_counter_offset = match instruction & 0xe0 {
            0x00 => self
                .machine
                .execute_operation::<false, false, false>(operation, self.program_counter),
            0x20 => self
                .machine
                .execute_operation::<true, false, false>(operation, self.program_counter),
            0x40 => self
                .machine
                .execute_operation::<false, true, false>(operation, self.program_counter),
            0x60 => self
                .machine
                .execute_operation::<true, true, false>(operation, self.program_counter),
            0x80 => self
                .machine
                .execute_operation::<false, false, true>(operation, self.program_counter),
            0xa0 => self
                .machine
                .execute_operation::<true, false, true>(operation, self.program_counter),
            0xc0 => self
                .machine
                .execute_operation::<false, true, false>(operation, self.program_counter),
            0xe0 => self
                .machine
                .execute_operation::<true, true, true>(operation, self.program_counter),
            _ => unreachable!("You managed to enter a set of modes that does not exist... huh?"),
        };

        if let Some(offset) = program_counter_offset {
            self.program_counter = self.program_counter.wrapping_add(offset);
            Some(instruction)
        } else {
            None
        }
    }
}
