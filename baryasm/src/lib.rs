//! # BaryAsm
//! An efficient [UxnTal](https://wiki.xxiivv.com/site/uxntal.html) assembler based on parser combinators.
//!
//! Meant as a companion to [BaryUxn](), does not require [`std`] or anything fancy:
//! just grab a stream of bytes and try to compile it into a UxnTal ROM!
//!
//! Uses [nom](https://crates.io/crates/nom) under the hood.
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

#![no_std]

use heapless::{FnvIndexMap, Vec};

#[cfg(test)]
mod test;

pub struct UxnTalAbstration {}

/// Keeps track of all information regarding the current assembly process.
#[derive(Default)]
pub struct UxnTalAssemblerContext<'a> {
    // Current line and file
    line: usize,
    file: &'a str,

    // Preprocessing information
    references: FnvIndexMap<&'a str, u16, 0x1000>,
    macros: Vec<(&'a str, &'a str), 0x1000>,
    labels: FnvIndexMap<&'a str, u16, 0x1000>,
}
impl<'a> UxnTalAssemblerContext<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register_macro(&mut self, name: &'a str, body: &'a str) -> Result<(), ()> {
        // Check that the macro doesn't already exist.
        if self.macros.iter().any(|(n, _)| *n == name) {
            return Err(());
        }
        self.macros.push((name, body)).map_err(|_| ())?;
        Ok(())
    }
    pub fn get_macro(&self, name: &'a str) -> Option<&'a str> {
        self.macros
            .iter()
            .find_map(|(n, _)| if *n == name { Some(*n) } else { None })
    }
}

type UxnTalParserResult<'a, T> = Result<(&'a str, T), UxnTalParserError<'a>>;

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Ord, Eq)]
pub enum UxnTalParserError<'a> {
    UnknownOperation(&'a str),
    UnknownMode(char),
    RedundantMode(char),
    UnfinishedComment,
    InvalidHexadecimalDigit(char),
    InvalidHexadecimalLength(u8),
    InvalidIdentifier(&'a str),
}

/// Parses a [UxnTal instruction](https://wiki.xxiivv.com/site/uxntal_opcodes.html)
/// in literal form to its byte representation.
fn parse_instruction<'a>(
    source: &'a str,
    _context: &mut UxnTalAssemblerContext,
) -> UxnTalParserResult<'a, u8> {
    let (operation, modes) = source.split_at(3);

    // TODO: make this case insensitive
    let mut instruction = match operation {
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
        _ => return UxnTalParserResult::Err(UxnTalParserError::UnknownOperation(operation)),
    };

    let mut modes_count = 0;
    for c in modes.chars() {
        match c {
            '2' => {
                if (instruction & 0x20) == 0 {
                    instruction |= 0x20
                } else {
                    return UxnTalParserResult::Err(UxnTalParserError::RedundantMode(c));
                }
            }
            'r' => {
                if (instruction & 0x40) == 0 {
                    instruction |= 0x40
                } else {
                    return UxnTalParserResult::Err(UxnTalParserError::RedundantMode(c));
                }
            }
            'k' => {
                if (instruction & 0x80) == 0 {
                    instruction |= 0x80
                } else {
                    return UxnTalParserResult::Err(UxnTalParserError::RedundantMode(c));
                }
            }
            _ => {
                if !c.is_whitespace() {
                    return UxnTalParserResult::Err(UxnTalParserError::UnknownMode(c));
                }
                break;
            }
        }
        modes_count += 1;
    }

    UxnTalParserResult::Ok((&modes[modes_count..], instruction))
}

/// Parses a single UxnTal comment.
fn parse_comment<'a>(
    source: &'a str,
    context: &mut UxnTalAssemblerContext,
) -> UxnTalParserResult<'a, ()> {
    let mut depth = 0;
    let mut skip = 0;
    for c in source.chars() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            '\n' => context.line += 1,
            _ => {}
        }
        skip += 1;
    }
    if depth != 0 {
        UxnTalParserResult::Err(UxnTalParserError::UnfinishedComment)
    } else {
        UxnTalParserResult::Ok((&source[skip + 1..], ()))
    }
}

/// Parses hexadecimal numbers of u to 16 bits.
/// Returns `true` if the number parsed is a short, false if its a byte.
fn parse_hexadecimal<'a>(
    source: &'a str,
    _context: &mut UxnTalAssemblerContext,
) -> UxnTalParserResult<'a, (bool, u16)> {
    let mut hex_count = 0u8;
    let mut value = 0u16;
    for c in source.chars().take(4) {
        if let Some(i) = c.to_digit(16) {
            value <<= 4;
            value |= i as u16;
        } else if c.is_whitespace() {
            break;
        } else {
            return UxnTalParserResult::Err(UxnTalParserError::InvalidHexadecimalDigit(c));
        }
        hex_count += 1
    }

    UxnTalParserResult::Ok((&source[hex_count as usize..], (hex_count > 2, value)))
}

/// Parses an identifier, used for macros, labels and such.
fn parse_identifier<'a>(
    source: &'a str,
    context: &mut UxnTalAssemblerContext,
) -> UxnTalParserResult<'a, &'a str> {
    let mut name_length = 0;
    for c in source.chars() {
        if c.is_ascii_whitespace() {
            break;
        }
        if !c.is_alphabetic() {
            return Err(UxnTalParserError::InvalidIdentifier(
                &source[..=name_length],
            ));
        }
        name_length += 1;
    }
    let (name, rest) = source.split_at(name_length);
    Ok((rest, name))
}

/// Parses the body of a macro.
fn parse_macro_body<'a>(
    source: &'a str,
    context: &mut UxnTalAssemblerContext,
) -> UxnTalParserResult<'a, &'a str> {
    let mut name_length = 0;
    for c in source.chars() {
        if c.is_ascii_whitespace() {
            break;
        }
        if !c.is_alphabetic() {
            return Err(UxnTalParserError::InvalidIdentifier(
                &source[..=name_length],
            ));
        }
        name_length += 1;
    }
    let (name, rest) = source.split_at(name_length);
    Ok((rest, name))
}

/// Writes a byte to the ROM.
fn write_byte<'a>(rom: &'a mut [u8], byte: u8) -> &'a mut [u8] {
    rom[0] = byte;
    &mut rom[1..]
}

/// Writes a short to the ROM.
fn write_short<'a>(rom: &'a mut [u8], short: u16) -> &'a mut [u8] {
    let [msb, lsb] = short.to_be_bytes();
    rom[0] = msb;
    rom[1] = lsb;
    &mut rom[2..]
}
pub fn parse<'a>(mut source: &'a str) -> UxnTalParserResult<'a, [u8; 0x10000]> {
    let mut rom = [0u8; 0x10000];
    let mut rom_pointer = 0x100;
    let write_byte_rom = |rom: &mut [u8], rom_pointer: &mut usize, value: u8| {
        rom[*rom_pointer] = value;
        *rom_pointer += 1;
    };
    let write_short_rom = |rom: &mut [u8], rom_pointer: &mut usize, value: u16| {
        let [msb, lsb] = value.to_be_bytes();
        rom[*rom_pointer] = msb;
        rom[*rom_pointer + 1] = lsb;
        *rom_pointer += 2;
    };

    let mut context = UxnTalAssemblerContext::new();

    let mut next_char = source.chars().nth(0);
    while let Some(char) = next_char {
        source = match char {
            '(' => {
                // Comment
                parse_comment(source, &mut context)?.0
            }
            '|' => {
                // Absolute padding rune
                let (rest, (_, value)) = parse_hexadecimal(&source[1..], &mut context)?;
                rom[rom_pointer..value as usize].fill(0);
                rom_pointer = value as usize;
                rest
            }
            '$' => {
                // Relative padding rune
                source
            }
            '@' => {
                // Parent label rune
                source
            }
            '&' => {
                // Child label rune
                source
            }
            ',' => {
                // Literal relative address rune
                source
            }
            '_' => {
                // Raw relative address rune
                source
            }
            '.' => {
                // Literal zero-page address rune
                source
            }
            '-' => {
                // Raw zero-page address rune
                source
            }
            ';' => {
                // Literal absolute address rune
                source
            }
            ':' => {
                // DEPRECATED: use '=' instead.
                panic!("DEPRECATED: ':' rune has been replaced with '='")
            }
            '=' => {
                // Raw literal address rune
                source
            }
            '!' => {
                // JMI rune
                source
            }
            '?' => {
                // JCI rune
                source
            }
            '#' => {
                // LIT rune
                let (rest, (is_u16, value)) = parse_hexadecimal(&source[1..], &mut context)?;
                if is_u16 {
                    write_byte_rom(&mut rom, &mut rom_pointer, 0xa0); // Write LIT2
                    write_short_rom(&mut rom, &mut rom_pointer, value);
                } else {
                    write_byte_rom(&mut rom, &mut rom_pointer, 0x80); // Write LIT
                    write_byte_rom(&mut rom, &mut rom_pointer, value as u8)
                }
                rest
            }
            '"' => {
                // Raw ASCII string
                let mut chars = 1;
                for c in source[1..].chars() {
                    if c.is_ascii_whitespace() {
                        break;
                    }
                    write_byte_rom(&mut rom, &mut rom_pointer, c as u8);
                    chars += 1;
                }
                &source[chars..]
            }
            '%' => {
                // Macro
                let (rest, name) = parse_identifier(&source[1..], &mut context)?;
                source
            }
            '}' => {
                // Lambda
                source
            }
            '~' => {
                // Include
                source
            }
            _ => {
                // Otherwise, the token can be a raw hexadecimal number, an instruction,
                // a macro call or a pure reference
                if char.is_whitespace() {
                    &source[1..]
                } else if let Ok((rest, instruction)) = parse_instruction(source, &mut context) {
                    write_byte_rom(&mut rom, &mut rom_pointer, instruction);
                    rest
                } else if let Ok((rest, (is_u16, value))) = parse_hexadecimal(source, &mut context)
                {
                    if is_u16 {
                        write_short_rom(&mut rom, &mut rom_pointer, value)
                    } else {
                        write_byte_rom(&mut rom, &mut rom_pointer, value as u8)
                    }
                    rest
                } else {
                    source
                }
                // if resolve_macrocall(&mut context).is_ok() {
                //     continue;
                // }
            }
        };
        next_char = source.chars().nth(0);
    }
    UxnTalParserResult::Ok((source, rom))
}
