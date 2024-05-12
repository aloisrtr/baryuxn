//! # BaryAsm
//! An efficient byte-stream oriented [UxnTal](https://wiki.xxiivv.com/site/uxntal.html) assembler.
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
//! "infinite" memory, good for you! Otherwise, pass in an arena-like allocator and you're
//! good to go on embedded devices!

#![no_std]

mod arena;

use arena::ArenaAllocator;
use either::*;
use heapless::{LinearMap, Vec};

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
    TokenTooLong,
    EmptyLabel,
    ReferenceLimitExceeded,
    LabelLimitExceeded,
    ReferenceToUnknownLabel,
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
enum UxnTalReferenceTag {
    Relative,
    ZeroPage,
    Absolute,
    NonQualified,
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
    scope: Vec<u8, 0x40>,
    references: Vec<(&'this [u8], UxnTalReferenceTag, u16), 0x1000>,
    labels: LinearMap<&'this [u8], u16, 0x1000>,
    _macros: LinearMap<&'this [u8], &'this [u8], 0x1000>,

    // Inner arena of the context, where strings are copied when needed
    arena: ArenaAllocator<'this, BYTES>,

    // Lookahead buffer
    lookahead: Vec<u8, 0x8>,
}
impl<'src, const BYTES: usize> Default for UxnTalAssembler<'src, BYTES> {
    fn default() -> Self {
        Self {
            line: 0,

            scope: Vec::default(),
            rom: [0; 0x10000],
            rom_pointer: 0x100,

            references: Vec::default(),
            _macros: LinearMap::default(),
            labels: LinearMap::default(),
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
        log::trace!("wrote byte: {byte:#04x} ({})", byte as char);
    }

    /// Writes a short to the ROM.
    fn write_short(&mut self, short: u16) {
        let [msb, lsb] = short.to_be_bytes();
        self.rom[self.rom_pointer as usize] = msb;
        self.rom[self.rom_pointer.wrapping_add(1) as usize] = lsb;
        self.rom_pointer = self.rom_pointer.wrapping_add(2);
        log::trace!("wrote short: {short:#06x}",);
    }

    /// Parses a [UxnTal instruction](https://wiki.xxiivv.com/site/uxntal_opcodes.html)
    /// in literal form to its byte representation.
    fn write_instruction<I: Iterator<Item = u8>>(
        &mut self,
        source: &mut I,
    ) -> UxnTalParserResult<u8> {
        self.lookahead.extend(source.take(3 - self.lookahead.len()));
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
            self.lookahead
                .push(mode)
                .map_err(|_| UxnTalAssemblerError::TokenTooLong)?;
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
                return UxnTalParserResult::Ok(if hex_count <= 2 {
                    Either::Left(value as u8)
                } else {
                    Either::Right(value)
                });
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
            self.lookahead
                .push(c)
                .map_err(|_| UxnTalAssemblerError::TokenTooLong)?;
            if let Some(i) = (c as char).to_digit(16) {
                value <<= 4;
                value += i as u16;
            } else if (c as char).is_whitespace() {
                return UxnTalParserResult::Ok(if hex_count <= 2 {
                    Either::Left(value as u8)
                } else {
                    Either::Right(value)
                });
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

    fn make_reference<I: Iterator<Item = u8>>(
        &mut self,
        source: &mut I,
        address: u16,
        rune: char,
    ) -> UxnTalParserResult<()> {
        self.arena.start_registering();

        if self.lookahead.is_empty() {
            match source.next().unwrap() as char {
                '{' => todo!("lambdas are not yet supported"),
                '&' | '/' => {
                    for &b in &self.scope {
                        self.arena.register(b);
                    }
                }
                c => {
                    self.arena.register(c as u8);
                }
            };
        } else {
            let mut lookahead = self.lookahead.iter().cloned();
            match lookahead.next().ok_or(UxnTalAssemblerError::EmptyLabel)? as char {
                '{' => todo!("lambdas are not yet supported"),
                '&' | '/' => {
                    for &b in &self.scope {
                        self.arena.register(b);
                    }
                }
                c => {
                    self.arena.register(c as u8);
                }
            }
            for b in lookahead {
                if (b as char).is_whitespace() {
                    break;
                }
                self.arena.register(b);
            }
        }
        while let Some(b) = source.next() {
            if (b as char).is_whitespace() {
                break;
            }
            self.arena.register(b);
        }
        let label = self.arena.end_registering().unwrap();
        log::trace!(
            "registered reference to label {}",
            core::str::from_utf8(label).unwrap()
        );
        let tag = match rune {
            '_' | ',' => UxnTalReferenceTag::Relative,
            '-' | '.' => UxnTalReferenceTag::ZeroPage,
            '=' | ';' => UxnTalReferenceTag::Absolute,
            _ => UxnTalReferenceTag::NonQualified,
        };
        self.references
            .push((label, tag, address))
            .map_err(|_| UxnTalAssemblerError::ReferenceLimitExceeded)?;
        Ok(())
    }

    fn make_label<I: Iterator<Item = u8>>(
        &mut self,
        source: &mut I,
        scoped: bool,
    ) -> UxnTalParserResult<&'this [u8]> {
        self.arena.start_registering();
        if scoped {
            for &b in &self.scope {
                self.arena.register(b)
            }
        }
        while let Some(b) = source.next() {
            if (b as char).is_whitespace() {
                break;
            }
            self.arena.register(b);
        }
        let name = self.arena.end_registering().unwrap();
        if name.is_empty() {
            return UxnTalParserResult::Err(UxnTalAssemblerError::EmptyLabel);
        }
        if self
            .labels
            .insert(name, self.rom_pointer)
            .map_err(|_| UxnTalAssemblerError::LabelLimitExceeded)?
            .is_some()
        {
            return UxnTalParserResult::Err(UxnTalAssemblerError::DuplicateLabel);
        }
        log::trace!(
            "registered label {} at address {:#06x}",
            core::str::from_utf8(name).unwrap(),
            self.rom_pointer
        );
        Ok(name)
    }

    /// Consumes the assembler struct to return either a fully assembled ROM or
    /// an error if anything goes wrong.
    pub fn parse<I: Iterator<Item = u8>>(
        mut self,
        mut source: I,
    ) -> UxnTalParserResult<[u8; 0x10000]> {
        // Preprocessing phase
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
                    let label = self.make_label(&mut source, false)?;
                    self.scope.clear();
                    self.scope.extend_from_slice(label).unwrap();
                    self.scope.push(b'/').unwrap();
                    log::trace!(
                        "scope is now {}",
                        core::str::from_utf8(self.scope.as_slice()).unwrap()
                    );
                }
                '&' => {
                    // Child label rune
                    self.make_label(&mut source, true)?;
                }
                ',' => {
                    // Literal relative address rune
                    self.make_reference(&mut source, self.rom_pointer.wrapping_add(1), c)?;
                    self.write_byte(0x80);
                    self.rom_pointer = self.rom_pointer.wrapping_add(1);
                }
                '_' => {
                    // Raw relative address rune
                    self.make_reference(&mut source, self.rom_pointer, c)?;
                    self.rom_pointer = self.rom_pointer.wrapping_add(1);
                }
                '.' => {
                    // Literal zero-page address rune
                    self.make_reference(&mut source, self.rom_pointer.wrapping_add(1), c)?;
                    self.write_byte(0x80);
                    self.rom_pointer = self.rom_pointer.wrapping_add(1);
                }
                '-' => {
                    // Raw zero-page address rune
                    self.make_reference(&mut source, self.rom_pointer, c)?;
                    self.rom_pointer = self.rom_pointer.wrapping_add(1);
                }
                ';' => {
                    // Literal absolute address rune
                    self.make_reference(&mut source, self.rom_pointer.wrapping_add(1), c)?;
                    self.write_byte(0xa0);
                    self.rom_pointer = self.rom_pointer.wrapping_add(2);
                }
                ':' => {
                    // DEPRECATED: use '=' instead.
                    panic!("DEPRECATED: ':' rune has been replaced with '='")
                }
                '=' => {
                    // Raw literal address rune
                    self.make_reference(&mut source, self.rom_pointer, c)?;
                    self.rom_pointer = self.rom_pointer.wrapping_add(2);
                }
                '!' => {
                    // JMI rune
                    self.make_reference(&mut source, self.rom_pointer.wrapping_add(1), c)?;
                    self.write_byte(0x40);
                    self.rom_pointer = self.rom_pointer.wrapping_add(2);
                }
                '?' => {
                    // JCI rune
                    self.make_reference(&mut source, self.rom_pointer.wrapping_add(1), c)?;
                    self.write_byte(0x20);
                    self.rom_pointer = self.rom_pointer.wrapping_add(2);
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
                    todo!()
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
                        // Could be a macro, otherwise create a reference
                        // TODO: check if macro call
                        self.make_reference(&mut source, self.rom_pointer.wrapping_add(1), ' ')?;
                        self.write_byte(0x60);
                        self.rom_pointer = self.rom_pointer.wrapping_add(2);
                    }
                }
            };
        }

        // Assembly
        for (label, tag, reference) in self.references.into_iter() {
            let target = *self
                .labels
                .get(label)
                .ok_or(UxnTalAssemblerError::ReferenceToUnknownLabel)?;
            log::trace!(
                "resolving reference to label {} at address {reference:#06x}, with tag {tag:?}",
                core::str::from_utf8(label).unwrap()
            );
            match tag {
                UxnTalReferenceTag::Relative => {
                    let difference = target.wrapping_sub(reference).wrapping_sub(2);
                    // TODO check if reference too far
                    self.rom[reference as usize] = difference as u8;
                    log::trace!("wrote relative offset {difference:#04x}");
                }
                UxnTalReferenceTag::ZeroPage => {
                    self.rom[reference as usize] = target as u8;
                    log::trace!("wrote zero-page address {target:#04x}");
                }
                UxnTalReferenceTag::Absolute => {
                    let [msb, lsb] = target.to_be_bytes();
                    self.rom[reference as usize] = msb;
                    self.rom[reference.wrapping_add(1) as usize] = lsb;
                    log::trace!("wrote absolute address {target:#06x}");
                }
                UxnTalReferenceTag::NonQualified => {
                    let difference = target.wrapping_sub(reference).wrapping_sub(2);
                    let [msb, lsb] = difference.to_be_bytes();
                    self.rom[reference as usize] = msb;
                    self.rom[reference.wrapping_add(1) as usize] = lsb;
                    log::trace!("wrote relative offset {difference:#06x}");
                }
            }
        }
        Ok(self.rom)
    }

    /// Helper methods to parse full strings.
    pub fn parse_string(self, source: &str) -> UxnTalParserResult<[u8; 0x10000]> {
        self.parse(source.as_bytes().into_iter().cloned())
    }
}
