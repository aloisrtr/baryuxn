//! # BarUxn
//! An implementation of the [Uxn stack machine](https://wiki.xxiivv.com/site/uxn.html)
//! designed to not rely on `std`.
//!
//! This means it can run on baremetal, and is thoroughly adaptable to any plateform.
//!
//! The source is also designed to be as readable as possible.

use core::str;
use std::ops::{Shl, Shr};

/// The Uxn machine, able to execute [Uxntal instructions](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
pub struct UxnMachine {
    work_stack: [u8; 256],
    work_pointer: u8,
    return_stack: [u8; 256],
    return_pointer: u8,

    memory: [u8; 0x10000],
    _devices: [(); 16],
}
impl Default for UxnMachine {
    fn default() -> Self {
        Self::new()
    }
}
impl UxnMachine {
    pub fn new() -> Self {
        Self {
            work_stack: [0; 256],
            work_pointer: 0,
            return_stack: [0; 256],
            return_pointer: 0,
            memory: [0; 0x10000],
            _devices: [(); 16],
        }
    }

    /// Creates a new [`UxnMachine`] with the given memory contents.
    pub fn with_memory_content(memory: &[u8]) -> Self {
        let mut uxn = Self::default();
        memory
            .iter()
            .zip(&mut uxn.memory)
            .for_each(|(src, dest)| *dest = *src);
        uxn
    }

    /// Executes a single Uxntal instruction, modifying the machine's state.
    ///
    /// Returns what the program counter should be after this instruction.
    pub fn execute(&mut self, program_counter: u16) -> Option<u16> {
        let instruction = UxnInstruction::from_bits(self.memory[program_counter as usize]).unwrap();

        // The stack to be worked on
        let (stack, pointer) = if instruction.return_mode() {
            (
                self.return_stack.as_mut_ptr(),
                std::ptr::from_mut(&mut self.return_pointer),
            )
        } else {
            (
                self.work_stack.as_mut_ptr(),
                std::ptr::from_mut(&mut self.work_pointer),
            )
        };

        let mut initial_pointer = unsafe { pointer.as_ref().cloned().unwrap() };
        let keep_pointer = if instruction.keep_mode() {
            std::ptr::from_mut(&mut initial_pointer)
        } else {
            pointer
        };

        // Define our general functions
        // Pops the byte on top of the stack.
        let pop_byte = || unsafe {
            *keep_pointer = (*keep_pointer).wrapping_sub(1);
            *stack.offset(*keep_pointer as isize)
        };
        // Pops the signed byte on top of the stack.
        let pop_signed_byte = || unsafe { std::mem::transmute::<_, i8>(pop_byte()) };
        // Pops the short on top of the stack.
        let pop_short = || u16::from_be_bytes([pop_byte(), pop_byte()]);
        // Pushes a byte on top of the stack.
        let push_byte = |byte: u8| unsafe {
            *pointer = (*pointer).wrapping_add(1);
            *stack.offset((*pointer).wrapping_sub(1) as isize) = byte
        };
        // Pushes a short on top of the stack.
        let push_short = |short: u16| {
            let [low, high] = short.to_be_bytes();
            push_byte(high);
            push_byte(low);
        };
        let mut push_short_return_stack = |short: u16| {
            let [low, high] = short.to_be_bytes();
            self.return_stack[self.return_pointer as usize] = high;
            self.return_pointer = self.return_pointer.wrapping_add(1);
            self.return_stack[self.return_pointer as usize] = low;
            self.return_pointer = self.return_pointer.wrapping_add(1);
        };

        // Execute the actual instruction
        match instruction.operation_code() {
            // General opcodes
            0x01 => {
                // INC
                if instruction.short_mode() {
                    push_short(pop_short().wrapping_add(1))
                } else {
                    push_byte(pop_byte().wrapping_add(1))
                }
            }
            0x02 => {
                // POP
                if instruction.short_mode() {
                    pop_short();
                } else {
                    pop_byte();
                }
            }
            0x03 => {
                // NIP
                if instruction.short_mode() {
                    let val = pop_short();
                    pop_short();
                    push_short(val);
                } else {
                    let val = pop_byte();
                    pop_byte();
                    push_byte(val);
                }
            }
            0x04 => {
                // SWP
                if instruction.short_mode() {
                    let a = pop_short();
                    let b = pop_short();
                    push_short(a);
                    push_short(b);
                } else {
                    let a = pop_byte();
                    let b = pop_byte();
                    push_byte(a);
                    push_byte(b);
                }
            }
            0x05 => {
                // ROT
                if instruction.short_mode() {
                    let a = pop_short();
                    let b = pop_short();
                    let c = pop_short();
                    push_short(b);
                    push_short(a);
                    push_short(c);
                } else {
                    let a = pop_byte();
                    let b = pop_byte();
                    let c = pop_byte();
                    push_byte(b);
                    push_byte(a);
                    push_byte(c);
                }
            }
            0x06 => {
                // DUP
                if instruction.short_mode() {
                    let val = pop_short();
                    push_short(val);
                    push_short(val);
                } else {
                    let val = pop_byte();
                    push_byte(val);
                    push_byte(val);
                }
            }
            0x07 => {
                // OVR
                if instruction.short_mode() {
                    let a = pop_short();
                    let b = pop_short();
                    push_short(b);
                    push_short(a);
                    push_short(b);
                } else {
                    let a = pop_byte();
                    let b = pop_byte();
                    push_byte(b);
                    push_byte(a);
                    push_byte(b);
                }
            }
            0x08 => {
                // EQU
                push_byte(if instruction.short_mode() {
                    pop_short() == pop_short()
                } else {
                    pop_byte() == pop_byte()
                } as u8)
            }
            0x09 => {
                // NEQ
                push_byte(if instruction.short_mode() {
                    pop_short() != pop_short()
                } else {
                    pop_byte() != pop_byte()
                } as u8)
            }
            0x0a => {
                // GTH
                push_byte(if instruction.short_mode() {
                    pop_short() < pop_short()
                } else {
                    pop_byte() < pop_byte()
                } as u8)
            }
            0x0b => {
                // LTH
                push_byte(if instruction.short_mode() {
                    pop_short() > pop_short()
                } else {
                    pop_byte() > pop_byte()
                } as u8)
            }
            0x0c => {
                // JMP
                return if instruction.short_mode() {
                    Some(program_counter.wrapping_add(pop_short()))
                } else {
                    Some(program_counter.wrapping_add_signed(pop_signed_byte() as i16))
                };
            }
            0x0d => {
                // JCN
                if pop_byte() != 0 {
                    return if instruction.short_mode() {
                        Some(program_counter.wrapping_add(pop_short()))
                    } else {
                        Some(program_counter.wrapping_add_signed(pop_signed_byte() as i16))
                    };
                }
            }
            0x0e => {
                // JSR
                let new_program_counter = if instruction.short_mode() {
                    Some(program_counter.wrapping_add(pop_short()))
                } else {
                    Some(program_counter.wrapping_add_signed(pop_signed_byte() as i16))
                };
                push_short_return_stack(program_counter);
                return new_program_counter;
            }
            0x0f => {
                // STH
                if instruction.short_mode() {
                    push_short_return_stack(pop_short());
                } else {
                    self.return_pointer = self.return_pointer.wrapping_sub(1);
                    self.return_stack[self.return_pointer as usize] = pop_byte();
                }
            }
            0x10 => {
                // LDZ
                let address = pop_byte();
                push_byte(self.memory[address as usize]);
            }
            0x11 => {
                // STZ
                let address = pop_byte();
                let value = pop_byte();
                self.memory[address as usize] = value;
            }
            0x12 => {
                // LDR
                let address = program_counter.wrapping_add_signed(pop_signed_byte() as i16);
                push_byte(self.memory[address as usize]);
            }
            0x13 => {
                // STR
                let address = program_counter.wrapping_add_signed(pop_signed_byte() as i16);
                let value = pop_byte();
                self.memory[address as usize] = value;
            }
            0x14 => {
                // LDA
                let address = pop_short();
                push_byte(self.memory[address as usize]);
            }
            0x15 => {
                // STA
                let address = pop_short();
                let value = pop_byte();
                self.memory[address as usize] = value;
            }
            0x16 => {
                // DEA
                todo!()
            }
            0x17 => {
                // DEO
                todo!()
            }
            0x18 => {
                // ADD
                if instruction.short_mode() {
                    push_short(pop_short().wrapping_add(pop_short()))
                } else {
                    push_byte(pop_byte().wrapping_add(pop_byte()))
                }
            }
            0x19 => {
                // SUB
                if instruction.short_mode() {
                    let rhs = pop_short();
                    let lhs = pop_short();
                    push_short(lhs.wrapping_sub(rhs))
                } else {
                    let rhs = pop_byte();
                    let lhs = pop_byte();
                    push_byte(lhs.wrapping_sub(rhs))
                }
            }
            0x1a => {
                // MUL
                if instruction.short_mode() {
                    push_short(pop_short().wrapping_mul(pop_short()))
                } else {
                    push_byte(pop_byte().wrapping_mul(pop_byte()))
                }
            }
            0x1b => {
                // DIV
                if instruction.short_mode() {
                    let rhs = pop_short();
                    let lhs = pop_short();
                    push_short(lhs.checked_div(rhs).unwrap_or(0))
                } else {
                    let rhs = pop_byte();
                    let lhs = pop_byte();
                    push_byte(lhs.checked_div(rhs).unwrap_or(0))
                }
            }
            0x1c => {
                // AND
                if instruction.short_mode() {
                    push_short(pop_short() & pop_short())
                } else {
                    push_byte(pop_byte() & pop_byte())
                }
            }
            0x1d => {
                // ORA
                if instruction.short_mode() {
                    push_short(pop_short() | pop_short())
                } else {
                    push_byte(pop_byte() | pop_byte())
                }
            }
            0x1e => {
                // EOR
                if instruction.short_mode() {
                    push_short(pop_short() ^ pop_short())
                } else {
                    push_byte(pop_byte() ^ pop_byte())
                }
            }
            0x1f => {
                // SFT
                let shift = pop_byte();
                let left = shift >> 4;
                let right = shift & 0xF;
                if instruction.short_mode() {
                    push_short(pop_short().shr(right).shl(left))
                } else {
                    push_byte(pop_byte().shr(right).shl(left))
                }
            }

            // Immediate opcodes
            0x00 => {
                // BRK
                return None;
            }
            0x20 => {
                // JCI
                self.work_pointer = self.work_pointer.wrapping_sub(1);
                return if self.work_stack[self.work_pointer as usize] != 0 {
                    Some(program_counter.wrapping_add(u16::from_be_bytes([
                        self.memory[program_counter.wrapping_add(1) as usize],
                        self.memory[program_counter.wrapping_add(2) as usize],
                    ])))
                } else {
                    Some(program_counter.wrapping_add(3))
                };
            }
            0x40 => {
                // JMI
                return Some(program_counter.wrapping_add(u16::from_be_bytes([
                    self.memory[program_counter.wrapping_add(1) as usize],
                    self.memory[program_counter.wrapping_add(2) as usize],
                ])));
            }
            0x60 => {
                // JSI
                push_short_return_stack(program_counter.wrapping_add(2));

                return Some(program_counter.wrapping_add(u16::from_be_bytes([
                    self.memory[program_counter.wrapping_add(1) as usize],
                    self.memory[program_counter.wrapping_add(2) as usize],
                ])));
            }
            0x80 | 0xa0 | 0xc0 | 0xe0 => {
                // LIT
                if instruction.short_mode() {
                    push_short(u16::from_be_bytes([
                        self.memory[program_counter.wrapping_add(1) as usize],
                        self.memory[program_counter.wrapping_add(2) as usize],
                    ]))
                } else {
                    push_byte(self.memory[program_counter.wrapping_add(1) as usize])
                }
                return Some(program_counter.wrapping_add(3));
            }

            _ => panic!(
                "unknown operation code: {:#x}",
                instruction.operation_code()
            ),
        }

        Some(program_counter.wrapping_add(1))
    }

    /// Executes an entire vector of instructions starting at a given program counter.
    pub fn execute_vector(&mut self, program_counter: u16) {
        let mut program_counter = Some(program_counter);
        'vector: loop {
            if let Some(pc) = program_counter {
                program_counter = self.execute(pc);
            } else {
                break 'vector;
            }
        }
    }
}

bitflags::bitflags! {
    /// Represents a [Uxntal instruction](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
    #[repr(transparent)]
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub struct UxnInstruction: u8 {
        const SHORT_MODE = 0b0010_0000;
        const RETURN_MODE = 0b0100_0000;
        const KEEP_MODE = 0b1000_0000;
        const OPERATION_MASK = 0b0001_1111;
    }
}
impl UxnInstruction {
    pub fn operation_code(self) -> u8 {
        let intersection = self.intersection(Self::OPERATION_MASK).bits();
        if intersection == 0x00 || intersection == 0x20 {
            self.bits()
        } else {
            self.intersection(Self::OPERATION_MASK).bits()
        }
    }
    pub fn short_mode(self) -> bool {
        self.intersects(Self::SHORT_MODE)
    }
    pub fn return_mode(self) -> bool {
        self.intersects(Self::RETURN_MODE)
    }
    pub fn keep_mode(self) -> bool {
        self.intersects(Self::KEEP_MODE)
    }
}
impl std::fmt::Debug for UxnInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}{}",
            match self.operation_code() {
                // General opcodes
                0x01 => "inc",
                0x02 => "pop",
                0x03 => "nip",
                0x04 => "swp",
                0x05 => "rot",
                0x06 => "dup",
                0x07 => "ovr",
                0x08 => "equ",
                0x09 => "neq",
                0x0a => "gth",
                0x0b => "lth",
                0x0c => "jmp",
                0x0d => "jcn",
                0x0e => "jsr",
                0x0f => "sth",
                0x10 => "ldz",
                0x11 => "stz",
                0x12 => "ldr",
                0x13 => "str",
                0x14 => "lda",
                0x15 => "sta",
                0x16 => "dea",
                0x17 => "deo",
                0x18 => "add",
                0x19 => "sub",
                0x1a => "mul",
                0x1b => "div",
                0x1c => "and",
                0x1d => "ora",
                0x1e => "eor",
                0x1f => "sft",

                // Immediate opcodes
                0x00 => "brk",
                0x20 => "jci",
                0x40 => "jmi",
                0x60 => "jsi",
                0x80 => "lit",
                _ => unreachable!(),
            },
            if self.short_mode() { "2" } else { "" },
            if self.keep_mode() { "k" } else { "" },
            if self.return_mode() { "r" } else { "" }
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn inc_test() {
        // LIT 0x12; INC
        let mut uxn = UxnMachine::with_memory_content(&[0x80, 0x12, 0x00, 0x01, 0x00]);
        uxn.execute_vector(0);
        assert_eq!(uxn.work_stack[0..uxn.work_pointer as usize], [0x13]);

        // LIT 0x12; INCk
        let mut uxn = UxnMachine::with_memory_content(&[0x80, 0x12, 0x00, 0x81, 0x00]);
        uxn.execute_vector(0);
        assert_eq!(uxn.work_stack[0..uxn.work_pointer as usize], [0x12, 0x13]);

        // LIT2 0x0001; INC2
        let mut uxn = UxnMachine::with_memory_content(&[0xa0, 0x00, 0x01, 0x21, 0x00]);
        uxn.execute_vector(0);
        assert_eq!(uxn.work_stack[0..uxn.work_pointer as usize], [0x02, 0x00]);

        // LIT2 0x0001; INC2k
        let mut uxn = UxnMachine::with_memory_content(&[0xa0, 0x00, 0x01, 0xa1, 0x00]);
        uxn.execute_vector(0);
        assert_eq!(
            uxn.work_stack[0..uxn.work_pointer as usize],
            [0x01, 0x00, 0x02, 0x00]
        );
    }
}
