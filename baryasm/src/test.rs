use heapless::{String, Vec};

use crate::*;

#[test]
fn test_parse_comment() {
    let mut context = UxnTalAssemblerContext::new();
    assert_eq!(
        parse_comment("( this is a comment )", &mut context),
        Ok(("", ()))
    );
    assert_eq!(
        parse_comment("(( this is a bad comment )", &mut context),
        Err(UxnTalParserError::UnfinishedComment)
    )
}

#[test]
fn test_parse_nested_comment() {
    let mut context = UxnTalAssemblerContext::new();
    assert_eq!(
        parse_comment("( this is a (nested) () comment )", &mut context),
        Ok(("", ()))
    );
}

#[test]
fn test_parse_hexadecimal() {
    let mut context = UxnTalAssemblerContext::new();
    assert_eq!(
        parse_hexadecimal("1af2", &mut context),
        Ok(("", (true, 0x1af2)))
    );
    assert_eq!(
        parse_hexadecimal("ff", &mut context),
        Ok(("", (false, 0xff)))
    );
    assert_eq!(
        parse_hexadecimal("fg", &mut context),
        Err(UxnTalParserError::InvalidHexadecimalDigit('g'))
    );
    assert_eq!(
        parse_hexadecimal("1aa", &mut context),
        Ok(("", (true, 0x01aa)))
    );
    assert_eq!(
        parse_hexadecimal("1aafd", &mut context),
        Ok(("d", (true, 0x1aaf)))
    );
}

#[test]
fn test_parse_instruction() {
    let mut context = UxnTalAssemblerContext::new();
    assert_eq!(parse_instruction("BRK", &mut context), Ok(("", 0x00)));
    assert_eq!(parse_instruction("STH", &mut context), Ok(("", 0x0f)));
    assert_eq!(parse_instruction("ADD2r", &mut context), Ok(("", 0x78)));
    assert_eq!(
        parse_instruction("BRK some stuff", &mut context),
        Ok((" some stuff", 0x00))
    );
    assert_eq!(
        parse_instruction("STH wow", &mut context),
        Ok((" wow", 0x0f))
    );
    assert_eq!(
        parse_instruction("ADD2kj", &mut context),
        Err(UxnTalParserError::UnknownMode('j'))
    );
    assert_eq!(
        parse_instruction("LITk", &mut context),
        Err(UxnTalParserError::RedundantMode('k'))
    );
}

#[test]
fn test_parse_lit_rune() {
    assert_eq!(parse("#a0").unwrap().1[0x100..0x102], [0x80, 0xa0]);
    assert_eq!(parse("#a0a0").unwrap().1[0x100..0x103], [0xa0, 0xa0, 0xa0]);
    assert_eq!(
        parse("#a0a0 #ff").unwrap().1[0x100..0x105],
        [0xa0, 0xa0, 0xa0, 0x80, 0xff]
    );
}

#[test]
fn test_parse_ascii() {
    assert_eq!(
        &String::from_utf8(
            Vec::<u8, 16>::from_slice(&parse("\"ohohimastringyay").unwrap().1[0x100..0x110])
                .unwrap()
        )
        .unwrap(),
        &"ohohimastringyay"
    )
}

#[test]
fn test_absolute_padding() {
    assert_eq!(
        parse("|105 #ff").unwrap().1[0x100..=0x106],
        [0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0xff]
    )
}

#[test]
fn test_parse_identifier() {
    assert_eq!(
        parse_identifier("modulo", &mut UxnTalAssemblerContext::new()),
        Ok(("", "modulo"))
    );
    assert_eq!(
        parse_identifier("modulo otherstuff", &mut UxnTalAssemblerContext::new()),
        Ok((" otherstuff", "modulo"))
    )
}
