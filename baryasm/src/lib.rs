//! # BaryAsm
//! An efficient [UxnTal](https://wiki.xxiivv.com/site/uxntal.html) assembler based on parser combinators.
//!
//! Meant as a companion to [BaryUxn](), does not require [`std`] or anything fancy:
//! just grab a stream of bytes and try to compile it into a UxnTal ROM!
//!
//! ## Concatenative parsing
//! UxnTal is [concatenative language](https://wiki.xxiivv.com/site/concatenative.html),
//! meaning that operations are performed in the sequence in which they are presented.
//! This is akin to assembly, to be honest, albeit more readable maybe.
//!
//! There are three phases to the parsing/assembly of UxnTal:
//! - preprocessing, where labels, macros and other niceties are parsed, stored in a map so that we can place them where needed later.
//! - resolving, where everything is placed correctly and the program is "layed out" as it would in the final ROM.
//! - assembly, where all the program is transformed into an array of bytes (ROM) to be used by an emulator.
//!
//! This assembler works on **byte streams**. What this means is that you do not
//! need to load the entire file in memory, just stream the characters as they come!
//! This is particularily useful to flash UxnTal programs over SPI, I2C or other communication
//! protocols, and is particularily suited to micro-controllers which can't necessarily
//! hold an entire source file in memory.
//!
//! ## Future work: the [`Allocator`](std::alloc::Allocator) trait
//! The original [uxnasm]() has the same approach, but fixes an arena type allocator
//! hard coded into the code. In the future, this library will allow you to come with your own
//! allocator using the [`Allocator`](std::alloc::Allocator) trait. If you've got
//! "infinite" memory, good for you! Otherwise, pass in an arena allocator and you're
//! good to go on embedded devices!

#![no_std]

mod arena;

use arena::ArenaAllocator;
use either::*;
use heapless::Vec;

#[cfg(test)]
mod test;

type UxnTalParserResult<T> = Result<T, UxnTalAssemblerError>;

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Ord, Eq)]
pub enum UxnTalAssemblerError {
    UnknownOperation,
    UnknownMode(char),
    RedundantMode(char),
    UnfinishedComment,
    InvalidHexadecimalDigit(char),
    InvalidIdentifier,
    DuplicateMacro,
    DuplicateLabel,
}

/// Keeps track of all information regarding the current assembly process.
#[derive(Clone, Debug)]
pub struct UxnTalAssembler<'this, const BYTES: usize> {
    // Current line of the file
    line: usize,

    // Created ROM
    rom: [u8; 0x10000],
    rom_pointer: u16,

    // Preprocessing information
    // TODO: Change these to a sort of tree-like implementation branching on byte values
    references: Vec<(&'this [u8], u16), 0x1000>,
    // IMPLEMENTATION: Macros are written with a prefix byte, either 0 if the macro
    // contains no scoped labels/macro/reference call (meaning it can be fully
    // compiled and the slice should be copied to the rom when calling it) or
    // 1 if it is kept in string form.
    macros: Vec<(&'this [u8], &'this [u8]), 0x1000>,
    labels: Vec<(&'this [u8], u16), 0x1000>,

    // Inner arena of the context, where strings are copied when needed
    arena: ArenaAllocator<BYTES>,

    // Lookahead buffer
    lookahead: Vec<u8, 0x8>,
}
impl<'src, const BYTES: usize> Default for UxnTalAssembler<'src, BYTES> {
    fn default() -> Self {
        Self {
            line: 0,

            rom: [0; 0x10000],
            rom_pointer: 0x100,

            references: Vec::default(),
            macros: Vec::default(),
            labels: Vec::default(),
            arena: ArenaAllocator::default(),
            lookahead: Vec::default(),
        }
    }
}
impl<'this, const BYTES: usize> UxnTalAssembler<'this, BYTES> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Writes a byte to the ROM.
    fn write_byte(&mut self, byte: u8) {
        self.rom[self.rom_pointer as usize] = byte;
        self.rom_pointer = self.rom_pointer.wrapping_add(1);
    }

    /// Writes a short to the ROM.
    fn write_short(&mut self, short: u16) {
        let [msb, lsb] = short.to_be_bytes();
        self.rom[self.rom_pointer as usize] = msb;
        self.rom[self.rom_pointer.wrapping_add(1) as usize] = lsb;
        self.rom_pointer = self.rom_pointer.wrapping_add(2);
    }

    /// Parses a [UxnTal instruction](https://wiki.xxiivv.com/site/uxntal_opcodes.html)
    /// in literal form to its byte representation.
    fn write_instruction<I: Iterator<Item = u8>>(
        &mut self,
        source: &mut I,
    ) -> UxnTalParserResult<u8> {
        self.lookahead.extend(source.take(3 - self.lookahead.len())); // TODO: better error
        if self.lookahead.len() < 3 {
            return Err(UxnTalAssemblerError::UnknownOperation);
        }
        let operation = &self.lookahead[0..3];

        let mut instruction = match core::str::from_utf8(operation).unwrap() {
            "BRK" => 0x00,
            "JCI" => 0x20,
            "JMI" => 0x40,
            "JSI" => 0x60,
            "LIT" => 0x80,
            "INC" => 0x01,
            "POP" => 0x02,
            "NIP" => 0x03,
            "SWP" => 0x04,
            "ROT" => 0x05,
            "DUP" => 0x06,
            "OVR" => 0x07,
            "EQU" => 0x08,
            "NEQ" => 0x09,
            "GTH" => 0x0a,
            "LTH" => 0x0b,
            "JMP" => 0x0c,
            "JCN" => 0x0d,
            "JSR" => 0x0e,
            "STH" => 0x0f,
            "LDZ" => 0x10,
            "STZ" => 0x11,
            "LDR" => 0x12,
            "STR" => 0x13,
            "LDA" => 0x14,
            "STA" => 0x15,
            "DEI" => 0x16,
            "DEO" => 0x17,
            "ADD" => 0x18,
            "SUB" => 0x19,
            "MUL" => 0x1a,
            "DIV" => 0x1b,
            "AND" => 0x1c,
            "ORA" => 0x1d,
            "EOR" => 0x1e,
            "SFT" => 0x1f,
            _ => return UxnTalParserResult::Err(UxnTalAssemblerError::UnknownOperation),
        };

        while let Some(mode) = source.next() {
            self.lookahead.push(mode).unwrap(); // TODO: better error
            match mode as char {
                '2' => {
                    if (instruction & 0x20) == 0 {
                        instruction |= 0x20
                    } else {
                        return UxnTalParserResult::Err(UxnTalAssemblerError::RedundantMode(
                            mode as char,
                        ));
                    }
                }
                'r' => {
                    if (instruction & 0x40) == 0 {
                        instruction |= 0x40
                    } else {
                        return UxnTalParserResult::Err(UxnTalAssemblerError::RedundantMode(
                            mode as char,
                        ));
                    }
                }
                'k' => {
                    if (instruction & 0x80) == 0 {
                        instruction |= 0x80
                    } else {
                        return UxnTalParserResult::Err(UxnTalAssemblerError::RedundantMode(
                            mode as char,
                        ));
                    }
                }
                _ => {
                    if !(mode as char).is_whitespace() {
                        return UxnTalParserResult::Err(UxnTalAssemblerError::UnknownMode(
                            mode as char,
                        ));
                    }
                    break;
                }
            }
        }

        self.write_byte(instruction);

        UxnTalParserResult::Ok(instruction)
    }

    /// Parses a single UxnTal comment, not doing anything with it.
    fn walk_comment<I: Iterator<Item = u8>>(&mut self, source: &mut I) -> UxnTalParserResult<()> {
        let mut depth = 1;
        for c in source {
            match c as char {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                '\n' => self.line += 1,
                _ => {}
            }
        }
        if depth != 0 {
            UxnTalParserResult::Err(UxnTalAssemblerError::UnfinishedComment)
        } else {
            UxnTalParserResult::Ok(())
        }
    }

    /// Parses hexadecimal numbers of up to 16 bits.
    fn parse_hexadecimal<I: Iterator<Item = u8>>(
        &mut self,
        source: &mut I,
    ) -> UxnTalParserResult<Either<u8, u16>> {
        let mut hex_count = 0u8;
        let mut value = 0u16;

        for &c in self.lookahead.iter() {
            if let Some(i) = (c as char).to_digit(16) {
                value <<= 4;
                value += i as u16;
            } else if (c as char).is_whitespace() {
                break;
            } else {
                return UxnTalParserResult::Err(UxnTalAssemblerError::InvalidHexadecimalDigit(
                    c as char,
                ));
            }
            hex_count += 1;
            if hex_count >= 4 {
                break;
            }
        }

        for c in source {
            self.lookahead.push(c).unwrap(); // TODO: better error
            if let Some(i) = (c as char).to_digit(16) {
                value <<= 4;
                value += i as u16;
            } else if (c as char).is_whitespace() {
                break;
            } else {
                return UxnTalParserResult::Err(UxnTalAssemblerError::InvalidHexadecimalDigit(
                    c as char,
                ));
            }
            hex_count += 1;
            if hex_count >= 4 {
                break;
            }
        }

        UxnTalParserResult::Ok(if hex_count <= 2 {
            Either::Left(value as u8)
        } else {
            Either::Right(value)
        })
    }

    // fn make_reference<I: Iterator<Item = u8>>(&mut self, source: &mut I) -> UxnTalParserResult<()> {
    //     // TODO: handle scopes and lambdas
    //     let name = self.arena.start_growable_alloc();
    //     let mut name_length = 0;
    //     let address = self.rom_pointer;

    //     // Parse the name
    //     for b in source {
    //         if (b as char).is_whitespace() {
    //             break;
    //         }
    //         name[name_length] = b;
    //         name_length += 1;
    //     }

    //     let (name, _) = name.split_at(name_length + 1);
    //     self.arena.end_growable_alloc(name);

    //     Ok(())
    // }

    /// Parses an identifier, used for macros, labels and such.
    // fn parse_identifier<'src>(
    //     source: &'src str,
    //     _context: &mut UxnTalAssembler,
    // ) -> UxnTalParserResult<'src, &'src str> {
    //     let mut name_length = 0;
    //     for c in source.chars() {
    //         if c.is_ascii_whitespace() {
    //             break;
    //         }
    //         if !c.is_alphabetic() {
    //             return Err(UxnTalParserError::InvalidIdentifier(
    //                 &source[..=name_length],
    //             ));
    //         }
    //         name_length += 1;
    //     }
    //     let (name, rest) = source.split_at(name_length);
    //     Ok((rest, name))
    // }

    /// Parses the body of a macro.
    fn register_macro<I: Iterator<Item = u8>>(&mut self, source: &mut I) -> UxnTalParserResult<()> {
        todo!()
    }

    /// Consumes the assembler struct to return either a fully assembled ROM or
    /// an error if anything goes wrong.
    pub fn parse<I: Iterator<Item = u8>>(
        mut self,
        mut source: I,
    ) -> UxnTalParserResult<[u8; 0x10000]> {
        while let Some(b) = source.next() {
            self.lookahead.clear();
            let c = b as char;
            match c {
                '(' => {
                    // Comment
                    self.walk_comment(&mut source)?;
                }
                '|' => {
                    // Absolute padding rune
                    let value = match self.parse_hexadecimal(&mut source)? {
                        Either::Left(value) => value as u16,
                        Either::Right(value) => value,
                    };
                    self.rom_pointer = value;
                }
                '$' => {
                    // Relative padding rune
                    let value = match self.parse_hexadecimal(&mut source)? {
                        Either::Left(value) => value as u16,
                        Either::Right(value) => value,
                    };
                    self.rom_pointer += value;
                }
                '@' => {
                    // Parent label rune
                    todo!()
                }
                '&' => {
                    // Child label rune
                    todo!()
                }
                ',' => {
                    // Literal relative address rune
                    todo!()
                }
                '_' => {
                    // Raw relative address rune
                    todo!()
                }
                '.' => {
                    // Literal zero-page address rune
                    todo!()
                }
                '-' => {
                    // Raw zero-page address rune
                    todo!()
                }
                ';' => {
                    // Literal absolute address rune
                    todo!()
                }
                ':' => {
                    // DEPRECATED: use '=' instead.
                    panic!("DEPRECATED: ':' rune has been replaced with '='")
                }
                '=' => {
                    // Raw literal address rune
                    todo!()
                }
                '!' => {
                    // JMI rune
                    todo!()
                }
                '?' => {
                    // JCI rune
                    todo!()
                }
                '#' => {
                    // LIT rune
                    let value = self.parse_hexadecimal(&mut source)?;
                    match value {
                        Either::Left(byte) => {
                            self.write_byte(0x80); // Write LIT
                            self.write_byte(byte)
                        }
                        Either::Right(short) => {
                            self.write_byte(0xa0); // Write LIT2
                            self.write_short(short);
                        }
                    }
                }
                '"' => {
                    // Raw ASCII string
                    while let Some(c) = &mut source.next() {
                        if (*c as char).is_ascii_whitespace() {
                            break;
                        }
                        self.write_byte(*c);
                    }
                }
                '%' => {
                    // Macro
                    // let (rest, (name, body)) = parse_macro_definition(&source[1..], context)?;
                    // context
                    //     .register_macro(name, body)
                    //     .map_err(|_| UxnTalParserError::DuplicateMacro(name))?;
                }
                '}' => {
                    // Lambda
                    todo!()
                }
                '~' => {
                    // Include
                    todo!()
                }
                '[' | ']' => {}
                _ if c.is_whitespace() => {}
                _ => {
                    // Otherwise, the token can be a raw hexadecimal number, an instruction,
                    // a macro call or a pure reference
                    self.lookahead.push(b).unwrap(); // TODO: better error
                    if self.write_instruction(&mut source).is_ok() {
                    } else if let Ok(value) = self.parse_hexadecimal(&mut source) {
                        match value {
                            Either::Left(byte) => self.write_byte(byte),
                            Either::Right(short) => self.write_short(short),
                        }
                    } else {
                        todo!()
                    }
                }
            };
        }
        Ok(self.rom)
    }

    /// Helper methods to parse full strings.
    pub fn parse_string(self, source: &str) -> UxnTalParserResult<[u8; 0x10000]> {
        self.parse(source.as_bytes().into_iter().cloned())
    }
}
