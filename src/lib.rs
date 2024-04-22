//! # BarUxn
//! An implementation of the [Uxn stack machine](https://wiki.xxiivv.com/site/uxn.html)
//! designed to not rely on `std`.
//!
//! This means it can run on baremetal, and is thoroughly adaptable to any plateform.
//!
//! The source is also designed to be as readable as possible.

#![no_std]

use core::ops::{Index, IndexMut};
use core::str;

pub trait UxnIndex {
    type Output;
    fn wrap(index: i8) -> Self;
}
impl UxnIndex for i8 {
    type Output = u8;
    fn wrap(index: i8) -> Self {
        index
    }
}

/// Specific index type indicating that we want to access bytes in a [`UxnStack`]
/// or memory. Equivalent to using an unwrapped [`i8`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteIndex {
    pub index: i8,
}
impl UxnIndex for ByteIndex {
    type Output = u8;
    fn wrap(index: i8) -> Self {
        Self { index }
    }
}
/// Specific index type indicating that we want to access shorts in a [`UxnStack`]
/// or memory.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShortIndex {
    pub index: i8,
}
impl UxnIndex for ShortIndex {
    type Output = u16;
    fn wrap(index: i8) -> Self {
        Self { index }
    }
}

/// Stack used by the [`UxnCpu`] to hold 255 bytes of data.
///
/// The interface is similar to that of a circular stack, with a fixed 255 element
/// size and some cut down functionnality.
///
/// All methods are provided with shorts alternatives, which as the name suggests
/// works on shorts rather than bytes.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct UxnStack {
    data: [u8; 0x100],
    pointer: u8,
}
impl Default for UxnStack {
    fn default() -> Self {
        Self::new()
    }
}
impl UxnStack {
    /// Returns an empty `UxnStack`.
    /// # Exemple
    /// ```rust
    /// ```
    pub const fn new() -> Self {
        Self {
            pointer: 0,
            data: [0u8; 0x100],
        }
    }

    /// Returns an iterator over the bytes of this stack, starting at the current
    /// position of the pointer.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn iter(&self) -> UxnStackIter<'_> {}

    /// Returns a mutable iterator over the bytes of this stack, starting at the current
    /// position of the pointer.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn iter_mut(&mut self) -> UxnStackIterMut<'_> {}

    /// Returns the byte at the current pointer location.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn current(&self) -> u8 {
        self.data[self.pointer as usize]
    }
    /// Returns a mutable reference to the byte at the current pointer location.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn current_mut(&mut self) -> &mut u8 {
        &mut self.data[self.pointer as usize]
    }

    /// Returns the byte at the given index, offset by the current pointer
    /// location.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn get(&self, index: i8) -> u8 {
        self.data[self.pointer.wrapping_add_signed(index) as usize]
    }

    /// Returns a mutable reference to the byte at the given index, offset by
    /// the current pointer location.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn get_mut(&mut self, index: i8) -> &mut u8 {
        &mut self.data[self.pointer.wrapping_add_signed(index) as usize]
    }

    /// Pushes a byte on top of the stack.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn push(&mut self, value: u8) {
        self.data[self.pointer as usize] = value;
        self.pointer = self.pointer.wrapping_add(1);
    }

    /// Pops a byte from the top of the stack.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn pop(&mut self) -> u8 {
        let value = self.data[self.pointer as usize];
        self.pointer = self.pointer.wrapping_sub(1);
        value
    }

    /// Pushes a short on top of the stack.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn push_short(&mut self, value: u16) {
        self.data[self.pointer as usize] = value;
        self.pointer = self.pointer.wrapping_add(1);
    }

    /// Pops a short from the top of the stack.
    /// # Exemple
    /// ```rust
    /// ```
    pub fn pop_short(&mut self) -> u16 {
        let value = self.data[self.pointer as usize];
        self.pointer = self.pointer.wrapping_sub(1);
        value
    }
}
impl Index<i8> for UxnStack {
    type Output = u8;
    fn index(&self, index: i8) -> &Self::Output {
        &self.data[self.pointer.wrapping_add_signed(index) as usize]
    }
}
impl IndexMut<i8> for UxnStack {
    fn index_mut(&mut self, index: i8) -> &mut Self::Output {
        &mut self.data[self.pointer.wrapping_add_signed(index) as usize]
    }
}
impl Index<ByteIndex> for UxnStack {
    type Output = u8;
    fn index(&self, index: ByteIndex) -> &Self::Output {
        self.index(index.index)
    }
}
impl IndexMut<ByteIndex> for UxnStack {
    fn index_mut(&mut self, index: ByteIndex) -> &mut Self::Output {
        self.index_mut(index.index)
    }
}
impl Index<ShortIndex> for UxnStack {
    type Output = u16;
    fn index(&self, index: ShortIndex) -> &Self::Output {
        todo!()
    }
}
impl IndexMut<ShortIndex> for UxnStack {
    fn index_mut(&mut self, index: ShortIndex) -> &mut Self::Output {
        todo!()
    }
}

/// Structures implementing the [`UxnDevice`] trait can be connected to the a [`UxnCpu`]
/// to offer external functionnality, such as displays, keyboards, etc.
pub trait UxnDevice {
    /// Reads a byte from the [`UxnDevice`].
    fn read(&mut self, address: u8) -> u8;
    /// Write a byte to the [`UxnDevice`].
    fn write(&mut self, address: u8, value: u8);

    fn read_slice(&mut self, address: u8, dest: &mut [u8]);
    fn write_slice(&mut self, address: u8, value: &[u8]);
}

/// The Uxn machine, able to execute [Uxntal instructions](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
pub struct UxnMachine<'a> {
    work_stack: UxnStack,
    return_stack: UxnStack,

    memory: [u8; 0x10000],
    devices: [Option<&'a dyn UxnDevice>; 16],
}
impl Default for UxnMachine<'_> {
    fn default() -> Self {
        Self::new()
    }
}
impl<'a> UxnMachine<'a> {
    /// Returns a new [`UxnMachine`] with no devices and a zeroed memory.
    pub fn new() -> Self {
        Self {
            work_stack: UxnStack::default(),
            return_stack: UxnStack::default(),
            memory: [0; 0x10000],
            devices: [None; 16],
        }
    }

    /// Modifies the memory contents of a [`UxnMachine`].
    pub fn with_memory_content(mut self, memory: &[u8]) -> Self {
        memory
            .iter()
            .zip(&mut self.memory)
            .for_each(|(src, dest)| *dest = *src);
        self
    }

    /// Adds a [`UxnDevice`] to the [`UxnMachine`], associating it with the given
    /// page.
    pub fn with_device(mut self, device: &'a dyn UxnDevice, page: u8) -> Self {
        self.devices[page as usize] = Some(device);
        self
    }

    /// Executes a single Uxntal instruction given a program counter, modifying the machine's state.
    ///
    /// Returns what the program counter should be after this instruction.
    pub fn execute(&mut self, program_counter: u16) -> Option<u16> {
        let instruction = self.memory[program_counter as usize];

        // Decode the instruction.
        let short_mode = (instruction & 0b0010_0000) != 0;
        let return_mode = (instruction & 0b0100_0000) != 0;
        let keep_mode = (instruction & 0b1000_0000) != 0;
        let is_immediate = (instruction & 0b0001_1111) == 0;
        let operation = if is_immediate {
            instruction
        } else {
            instruction & 0b0001_1111
        };

        // The stack to be worked on.
        let stack = if return_mode {
            &mut self.return_stack
        } else {
            &mut self.work_stack
        };

        // Execute the actual instruction
        match operation {
            // Immediate opcodes
            0x00 => {
                // BRK
                return None;
            }
            0x20 => {
                // JCI
                return if self.work_stack.pop() == 0 {
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
                self.return_stack
                    .push(self.memory[program_counter.wrapping_add(2) as usize]);

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

            // General opcodes
            0x01 => {
                // INC
                stack[0] = stack[0].wrapping_add(1);
                if short_mode {
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
                // DEI
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
impl core::fmt::Debug for UxnInstruction {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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
