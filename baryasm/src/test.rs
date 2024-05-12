extern crate std;

use std::sync::Once;

use heapless::String;

use crate::*;

static INIT: Once = Once::new();

fn init() {
    INIT.call_once(|| {
        env_logger::init();
    })
}

#[test]
fn test_parse_comment() {
    init();
    let mut assembler = UxnTalAssembler::<'_, 0x0>::new();
    assert!(assembler
        .walk_comment(&mut b" this is a comment )".iter().cloned())
        .is_ok());
    assert_eq!(
        assembler.walk_comment(&mut b"( this is a bad comment )".iter().cloned()),
        Err(UxnTalAssemblerError::UnfinishedComment)
    )
}

#[test]
fn test_parse_nested_comment() {
    init();
    let mut assembler = UxnTalAssembler::<'_, 0x0>::new();
    assert!(assembler
        .walk_comment(&mut b" this is a (nested) () comment )".iter().cloned())
        .is_ok());
}

#[test]
fn test_parse_hexadecimal() {
    init();
    let mut assembler = UxnTalAssembler::<'_, 0x0>::new();
    assembler.lookahead.clear();
    assert_eq!(
        assembler.parse_hexadecimal(&mut b"1Af2".iter().cloned()),
        Ok(Either::Right(0x1af2))
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.parse_hexadecimal(&mut b"FF".iter().cloned()),
        Ok(Either::Left(0xff))
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.parse_hexadecimal(&mut b"Fg".iter().cloned()),
        Err(UxnTalAssemblerError::InvalidHexadecimalDigit('g'))
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.parse_hexadecimal(&mut b"1AA".iter().cloned()),
        Ok(Either::Right(0x1aa))
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.parse_hexadecimal(&mut b"1Afd8".iter().cloned()),
        Ok(Either::Right(0x1afd))
    );
}

#[test]
fn test_parse_instruction() {
    init();
    let mut assembler = UxnTalAssembler::<'_, 0>::new();
    assert_eq!(
        assembler.write_instruction(&mut b"BRK".iter().cloned()),
        Ok(0x00)
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.write_instruction(&mut b"STH".iter().cloned()),
        Ok(0x0f)
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.write_instruction(&mut b"ADD2r".iter().cloned()),
        Ok(0x78)
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.write_instruction(&mut b"BRK some stuff".iter().cloned()),
        Ok(0x00)
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.write_instruction(&mut b"STH wow".iter().cloned()),
        Ok(0x0f)
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.write_instruction(&mut b"ADD2kj".iter().cloned()),
        Err(UxnTalAssemblerError::UnknownMode('j'))
    );
    assembler.lookahead.clear();
    assert_eq!(
        assembler.write_instruction(&mut b"LITk".iter().cloned()),
        Err(UxnTalAssemblerError::RedundantMode('k'))
    );
}

#[test]
fn test_parse_lit_rune() {
    init();
    let assembler = UxnTalAssembler::<'_, 0>::new();
    assert_eq!(
        assembler.parse_string("#Ff").unwrap()[0x100..0x102],
        [0x80, 0xff]
    );
}

#[test]
fn test_parse_lit2_rune() {
    init();
    let assembler = UxnTalAssembler::<'_, 0>::new();
    assert_eq!(
        assembler.parse_string("#faF9").unwrap()[0x100..0x103],
        [0xa0, 0xfa, 0xf9]
    );
}

#[test]
fn test_parse_ascii() {
    init();
    let assembler = UxnTalAssembler::<'_, 0>::new();
    assert_eq!(
        &String::from_utf8(
            Vec::<u8, 16>::from_slice(
                &assembler.parse_string("\"ohohimastringyay").unwrap()[0x100..0x110]
            )
            .unwrap()
        )
        .unwrap(),
        &"ohohimastringyay"
    )
}

#[test]
fn test_absolute_padding() {
    init();
    let assembler = UxnTalAssembler::<'_, 0>::new();
    assert_eq!(
        assembler.parse_string("|10 #ff").unwrap()[0x10..0x12],
        [0x80, 0xff]
    )
}

#[test]
fn test_relative_padding() {
    init();
    let assembler = UxnTalAssembler::<'_, 0>::new();
    assert_eq!(
        assembler.parse_string("$5 #ff").unwrap()[0x105..0x107],
        [0x80, 0xff]
    )
}

/*
 * GENERAL INTEGRATION TESTING
 */

#[test]
fn test_result_six() {
    init();
    let rom = UxnTalAssembler::<'_, 0>::new()
        .parse_string("#01 DUP ADD #03 MUL ( result: 06 )")
        .unwrap();
    assert_eq!(
        rom[0x100..0x107],
        [0x80, 0x01, 0x06, 0x18, 0x80, 0x03, 0x1a]
    );
}

#[test]
fn test_hello_world_example() {
    init();
    let rom = UxnTalAssembler::<'_, 0x10000>::new()
        .parse_string(
            r#"
        |10 @Console &vector $2 &read $1 &pad $5 &write $1 &error $1

        |100

        @on-reset ( -> )
        	;my-string print-text
        	BRK

        @print-text ( str* -- )
        	&while
        		LDAk .Console/write DEO
        		INC2 LDAk ?&while
        	POP2
        	JMP2r

        @my-string
        	"Hello 20 "World! 00
    "#,
        )
        .unwrap();

    assert_eq!(
        rom[0x100..0x11f],
        [
            0xa0, 0x01, 0x12, 0x60, 0x00, 0x01, 0x00, 0x94, 0x80, 0x18, 0x17, 0x21, 0x94, 0x20,
            0xff, 0xf7, 0x22, 0x6c, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72, 0x6c,
            0x64, 0x21, 0x00
        ]
    )
}
