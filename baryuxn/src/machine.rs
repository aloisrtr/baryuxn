use core::ops::{Index, IndexMut};

use crate::stack::UxnStack;
/// The Uxn machine, able to execute [Uxntal instructions](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
pub struct UxnMachine<T> {
    work_stack: UxnStack,
    return_stack: UxnStack,

    memory: T,
    device_bus: (),
}
impl<T> Default for UxnMachine<T>
where
    T: Default,
{
    fn default() -> Self {
        Self::new()
    }
}
impl<T> UxnMachine<T>
where
    T: Default,
{
    /// Returns a new [`UxnMachine`] with no devices and default memory (depends on
    /// the implementation of [`T`]).
    pub fn new() -> Self {
        Self {
            work_stack: UxnStack::default(),
            return_stack: UxnStack::default(),
            memory: T::default(),
            device_bus: (),
        }
    }
}
impl<T> UxnMachine<T>
where
    T: Index<u16, Output = u8> + IndexMut<u16>,
{
    /// Modifies the memory contents of a [`UxnMachine`].
    pub fn with_memory(mut self, memory: T) -> Self {
        self.memory = memory;
        self
    }

    /// Adds a [`UxnDevice`] to the [`UxnMachine`], associating it with the given
    /// page.
    // pub fn with_device(mut self, device: &'a dyn UxnDevice, page: u8) -> Self {
    //     self.devices[page as usize] = Some(device);
    //     self
    // }

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
                        return Some(program_counter.wrapping_add(2));
                    }
                    (true, _, true) => {
                        // LIT2
                        stack.push_short(Self::get_memory_short(
                            &self.memory,
                            program_counter.wrapping_add(1),
                        ));
                        return Some(program_counter.wrapping_add(2));
                    }
                }
            }

            // General opcodes
            0x01 => {
                // INC
                if SHORT {
                    let v = stack.pop_short().wrapping_add(1);
                    stack.push_short(v)
                } else {
                    let v = stack.pop().wrapping_add(1);
                    stack.push(v)
                }
            }
            0x02 => {
                // POP
                if SHORT {
                    stack.pop_short();
                } else {
                    stack.pop();
                }
            }
            0x03 => {
                // NIP
                if SHORT {
                    stack.remove_short(-2);
                } else {
                    stack.remove(-1);
                }
            }
            0x04 => {
                // SWP
                if SHORT {
                    let v = stack.remove_short(-2);
                    stack.push_short(v);
                } else {
                    let v = stack.remove(-1);
                    stack.push(v);
                }
            }
            0x05 => {
                // ROT
                if SHORT {
                    let v = stack.remove_short(-4);
                    stack.push_short(v);
                } else {
                    let v = stack.remove(-2);
                    stack.push(v)
                }
            }
            0x06 => {
                // DUP
                if SHORT {
                    let v = stack.pop_short();
                    stack.push_short(v);
                    stack.push_short(v);
                } else {
                    let v = stack.pop();
                    stack.push(v);
                    stack.push(v);
                }
            }
            0x07 => {
                // OVR
                if SHORT {
                    let v = stack.get_short(-2);
                    stack.push_short(v)
                } else {
                    let v = stack.get(-1);
                    stack.push(v)
                }
            }
            0x08 => {
                // EQU
                let res = if SHORT {
                    stack.pop_short() == stack.pop_short()
                } else {
                    stack.pop() == stack.pop()
                } as u8;
                stack.push(res);
            }
            0x09 => {
                // NEQ
                let res = if SHORT {
                    stack.pop_short() != stack.pop_short()
                } else {
                    stack.pop() != stack.pop()
                } as u8;
                stack.push(res);
            }
            0x0a => {
                // GTH
                let res = if SHORT {
                    stack.pop_short() < stack.pop_short()
                } else {
                    stack.pop() < stack.pop()
                } as u8;
                stack.push(res);
            }
            0x0b => {
                // LTH
                let res = if SHORT {
                    stack.pop_short() > stack.pop_short()
                } else {
                    stack.pop() > stack.pop()
                } as u8;
                stack.push(res);
            }
            0x0c => {
                // JMP
                return Some(if SHORT {
                    stack.pop_short().wrapping_sub(program_counter)
                } else {
                    program_counter.wrapping_add((stack.pop() as i8) as u16)
                });
            }
            0x0d => {
                // JCN
                if stack.pop() != 0 {
                    return Some(if SHORT {
                        stack.pop_short().wrapping_sub(program_counter)
                    } else {
                        program_counter.wrapping_add((stack.pop() as i8) as u16)
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
                        stack.pop_short().wrapping_sub(program_counter)
                    } else {
                        program_counter.wrapping_add((stack.pop() as i8) as u16)
                    });
                } else {
                    self.return_stack.push_short(program_counter);
                    return Some(if SHORT {
                        self.work_stack.pop_short().wrapping_sub(program_counter)
                    } else {
                        program_counter.wrapping_add((self.work_stack.pop() as i8) as u16)
                    });
                };
            }
            0x0f => {
                // STH
                if SHORT {
                    let v = stack.pop_short();
                    if RETURN {
                        self.work_stack.push_short(v)
                    } else {
                        self.return_stack.push_short(v)
                    }
                } else {
                    let v = stack.pop();
                    if RETURN {
                        self.work_stack.push(v)
                    } else {
                        self.return_stack.push(v)
                    }
                }
            }
            0x10 => {
                // LDZ
                let address = stack.pop();
                if SHORT {
                    stack.push_short(Self::get_memory_short(&self.memory, address as u16))
                } else {
                    stack.push(Self::get_memory(&self.memory, address as u16))
                }
            }
            0x11 => {
                // STZ
                let address = stack.pop();
                if SHORT {
                    let v = stack.pop_short();
                    Self::set_memory_short_mut(&mut self.memory, address as u16, v)
                } else {
                    let v = stack.pop();
                    *Self::get_memory_mut(&mut self.memory, address as u16) = v
                }
            }
            0x12 => {
                // LDR
                let address = program_counter.wrapping_add_signed((stack.pop() as i8) as i16);
                if SHORT {
                    stack.push_short(Self::get_memory_short(&self.memory, address as u16))
                } else {
                    stack.push(Self::get_memory(&self.memory, address as u16))
                }
            }
            0x13 => {
                // STR
                let address = program_counter.wrapping_add((stack.pop() as i8) as u16);
                if SHORT {
                    let v = stack.pop_short();
                    Self::set_memory_short_mut(&mut self.memory, address as u16, v)
                } else {
                    let v = stack.pop();
                    *Self::get_memory_mut(&mut self.memory, address as u16) = v
                }
            }
            0x14 => {
                // LDA
                let address = stack.pop_short();
                if SHORT {
                    stack.push_short(Self::get_memory_short(&self.memory, address as u16))
                } else {
                    stack.push(Self::get_memory(&self.memory, address as u16))
                }
            }
            0x15 => {
                // STA
                let address = stack.pop_short();
                if SHORT {
                    let v = stack.pop_short();
                    Self::set_memory_short_mut(&mut self.memory, address as u16, v)
                } else {
                    let v = stack.pop();
                    *Self::get_memory_mut(&mut self.memory, address as u16) = v
                }
            }
            0x16 => {
                // DEI
                todo!()
            }
            0x17 => {
                // DEO
                todo!()
            }
            0x18 => {
                // ADD
                if SHORT {
                    let a = stack.pop_short();
                    let b = stack.pop_short();
                    stack.push_short(a.wrapping_add(b));
                } else {
                    let a = stack.pop();
                    let b = stack.pop();
                    stack.push(a.wrapping_add(b));
                }
            }
            0x19 => {
                // SUB
                if SHORT {
                    let b = stack.pop_short();
                    let a = stack.pop_short();
                    stack.push_short(a.wrapping_sub(b));
                } else {
                    let b = stack.pop();
                    let a = stack.pop();
                    stack.push(a.wrapping_sub(b));
                }
            }
            0x1a => {
                // MUL
                if SHORT {
                    let a = stack.pop_short();
                    let b = stack.pop_short();
                    stack.push_short(a.wrapping_mul(b));
                } else {
                    let a = stack.pop();
                    let b = stack.pop();
                    stack.push(a.wrapping_mul(b));
                }
            }
            0x1b => {
                // DIV
                if SHORT {
                    let b = stack.pop_short();
                    let a = stack.pop_short();
                    if b == 0 {
                        stack.push_short(0)
                    } else {
                        stack.push_short(a.wrapping_div(b));
                    }
                } else {
                    let b = stack.pop();
                    let a = stack.pop();
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
                    let a = stack.pop_short();
                    let b = stack.pop_short();
                    stack.push_short(a & b);
                } else {
                    let a = stack.pop();
                    let b = stack.pop();
                    stack.push(a & b);
                }
            }
            0x1d => {
                // ORA
                if SHORT {
                    let a = stack.pop_short();
                    let b = stack.pop_short();
                    stack.push_short(a | b);
                } else {
                    let a = stack.pop();
                    let b = stack.pop();
                    stack.push(a | b);
                }
            }
            0x1e => {
                // EOR
                if SHORT {
                    let a = stack.pop_short();
                    let b = stack.pop_short();
                    stack.push_short(a ^ b);
                } else {
                    let a = stack.pop();
                    let b = stack.pop();
                    stack.push(a ^ b);
                }
            }
            0x1f => {
                // SFT
                let shift = stack.pop();
                let shift_right = 0x0f & shift;
                let shift_left = (0xf0 & shift) >> 4;
                if SHORT {
                    let v = stack.pop_short();
                    stack.push_short((v >> shift_right) << shift_left)
                } else {
                    let v = stack.pop();
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
pub struct UxnVector<'a, T> {
    pub(crate) machine: &'a mut UxnMachine<T>,
    pub(crate) program_counter: u16,
}
impl<'a, T> Iterator for UxnVector<'a, T>
where
    T: Index<u16, Output = u8> + IndexMut<u16>,
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
