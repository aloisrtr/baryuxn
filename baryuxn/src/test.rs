use core::ops::{Index, IndexMut};

use baryasm::UxnTalAssembler;

use crate::{bus::UxnDeviceBus, machine::*};

struct UxnRom([u8; 0x10000]);
impl Index<u16> for UxnRom {
    type Output = u8;
    fn index(&self, index: u16) -> &Self::Output {
        &self.0[index as usize]
    }
}
impl IndexMut<u16> for UxnRom {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        &mut self.0[index as usize]
    }
}

struct UxnTestBus([u8; 0x100]);
impl<T> UxnDeviceBus<T> for UxnTestBus {
    fn read(&mut self, _machine: &mut UxnMachine<T>, address: u8) -> u8 {
        self.0[address as usize]
    }
    fn write(&mut self, _machine: &mut UxnMachine<T>, address: u8, byte: u8) {
        self.0[address as usize] = byte
    }
}

fn machine_from_source(source: &str) -> UxnMachine<UxnRom> {
    let rom = UxnTalAssembler::<'_, 0>::new()
        .parse_string(source)
        .unwrap();
    UxnMachine::new(UxnRom(rom))
}
fn assert_work_stack_state(source: &str, expected_stack: &[u8]) {
    let mut machine = machine_from_source(source);
    machine.execute_vector(0x100, &mut UxnTestBus([0; 0x100]));
    assert_eq!(
        &machine.work_stack.data[..expected_stack.len()],
        expected_stack
    )
}
fn assert_return_stack_state(source: &str, expected_stack: &[u8]) {
    let mut machine = machine_from_source(source);
    machine.execute_vector(0x100, &mut UxnTestBus([0; 0x100]));
    assert_eq!(
        &machine.return_stack.data[..expected_stack.len()],
        expected_stack
    )
}

#[test]
fn test_lit() {
    assert_work_stack_state("LIT 12", &[0x12]);
    assert_work_stack_state("LIT2 abcd", &[0xab, 0xcd]);
}

#[test]
fn test_inc() {
    assert_work_stack_state("#01 INC", &[0x02]);
    assert_work_stack_state("#0001 INC2", &[0x00, 0x02]);
    assert_work_stack_state("#0001 INC2k", &[0x00, 0x01, 0x00, 0x02]);
}

#[test]
fn test_pop() {
    assert_work_stack_state("#1234 POP", &[0x12]);
    assert_work_stack_state("#1234 POP2", &[]);
    assert_work_stack_state("#1234 POP2k", &[0x12, 0x34]);
}

#[test]
fn test_nip() {
    assert_work_stack_state("#1234 NIP", &[0x34]);
    assert_work_stack_state("#1234 #5678 NIP2", &[0x56, 0x78]);
    assert_work_stack_state("#1234 #5678 NIP2k", &[0x12, 0x34, 0x56, 0x78, 0x56, 0x78]);
}

#[test]
fn test_swp() {
    assert_work_stack_state("#1234 SWP", &[0x34, 0x12]);
    assert_work_stack_state("#1234 SWPk", &[0x12, 0x34, 0x34, 0x12]);
    assert_work_stack_state("#1234 #5678 SWP2", &[0x56, 0x78, 0x12, 0x34]);
    assert_work_stack_state(
        "#1234 #5678 SWP2k",
        &[0x12, 0x34, 0x56, 0x78, 0x56, 0x78, 0x12, 0x34],
    );
}

#[test]
fn test_rot() {
    assert_work_stack_state("#1234 #56 ROT", &[0x34, 0x56, 0x12]);
    assert_work_stack_state("#1234 #56 ROTk", &[0x12, 0x34, 0x56, 0x34, 0x56, 0x12]);
    assert_work_stack_state(
        "#1234 #5678 #9abc ROT2",
        &[0x56, 0x78, 0x9a, 0xbc, 0x12, 0x34],
    );
    assert_work_stack_state(
        "#1234 #5678 #9abc ROT2k",
        &[
            0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0x56, 0x78, 0x9a, 0xbc, 0x12, 0x34,
        ],
    );
}

#[test]
fn test_dup() {
    assert_work_stack_state("#1234 DUP", &[0x12, 0x34, 0x34]);
    assert_work_stack_state("#12 DUPk", &[0x12, 0x12, 0x12]);
    assert_work_stack_state("#1234 DUP2", &[0x12, 0x34, 0x12, 0x34]);
}

#[test]
fn test_ovr() {
    assert_work_stack_state("#1234 OVR", &[0x12, 0x34, 0x12]);
    assert_work_stack_state("#1234 OVRk", &[0x12, 0x34, 0x12, 0x34, 0x12]);
    assert_work_stack_state("#1234 #5678 OVR2", &[0x12, 0x34, 0x56, 0x78, 0x12, 0x34]);
    assert_work_stack_state(
        "#1234 #5678 OVR2k",
        &[0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34],
    );
}

#[test]
fn test_equ() {
    assert_work_stack_state("#1212 EQU", &[0x01]);
    assert_work_stack_state("#1234 EQUk", &[0x12, 0x34, 0x00]);
    assert_work_stack_state("#abcd #ef01 EQU2", &[0x00]);
    assert_work_stack_state("#abcd #abcd EQU2k", &[0xab, 0xcd, 0xab, 0xcd, 0x01]);
}

#[test]
fn test_neq() {
    assert_work_stack_state("#1212 NEQ", &[0x00]);
    assert_work_stack_state("#1234 NEQk", &[0x12, 0x34, 0x01]);
    assert_work_stack_state("#abcd #ef01 NEQ2", &[0x01]);
    assert_work_stack_state("#abcd #abcd NEQ2k", &[0xab, 0xcd, 0xab, 0xcd, 0x00]);
}

#[test]
fn test_gth() {
    assert_work_stack_state("#1234 GTH", &[0x00]);
    assert_work_stack_state("#3412 GTHk", &[0x34, 0x12, 0x01]);
    assert_work_stack_state("#3456 #1234 GTH2", &[0x01]);
    assert_work_stack_state("#1234 #3456 GTH2k", &[0x12, 0x34, 0x34, 0x56, 0x00]);
}

#[test]
fn test_lth() {
    assert_work_stack_state("#0101 LTH", &[0x00]);
    assert_work_stack_state("#0100 LTHk", &[0x01, 0x00, 0x00]);
    assert_work_stack_state("#0001 #0000 LTH2", &[0x00]);
    assert_work_stack_state("#0001 #0000 LTH2k", &[0x00, 0x01, 0x00, 0x00, 0x00]);
}

#[test]
fn test_jmp() {
    todo!()
}

#[test]
fn test_jcn() {
    todo!()
}

#[test]
fn test_jsr() {
    todo!()
}

#[test]
fn test_sth() {
    assert_return_stack_state("#12 STH", &[0x12]);
    //assert_work_stack_state("LITr 34 STHr", &[0x34]);
}

#[test]
fn test_ldz() {
    todo!()
}

#[test]
fn test_stz() {
    todo!()
}

#[test]
fn test_ldr() {
    todo!()
}

#[test]
fn test_str() {
    todo!()
}

#[test]
fn test_lda() {
    todo!()
}

#[test]
fn test_sta() {
    todo!()
}

#[test]
fn test_dei() {
    let mut devices = UxnTestBus([0; 0x100]);
    devices.0[0x10] = 0x34;
    devices.0[0x11] = 0x56;
    let mut machine = machine_from_source("#10 DEI");
    machine.execute_vector(0x100, &mut devices);
    assert_eq!(machine.work_stack.data[0], 0x34);

    let mut machine = machine_from_source("#10 DEIk");
    machine.execute_vector(0x100, &mut devices);
    assert_eq!(&machine.work_stack.data[0..2], &[0x10, 0x34]);

    let mut machine = machine_from_source("#10 DEI2");
    machine.execute_vector(0x100, &mut devices);
    assert_eq!(&machine.work_stack.data[0..2], &[0x34, 0x56]);
}

#[test]
fn test_deo() {
    let mut devices = UxnTestBus([0; 0x100]);
    devices.0[0x10] = 0x34;
    devices.0[0x11] = 0x56;
    let mut machine = machine_from_source("#20 #10 DEO");
    machine.execute_vector(0x100, &mut devices);
    assert_eq!(devices.0[0x10], 0x20);

    let mut machine = machine_from_source("#20 #10 DEOk");
    machine.execute_vector(0x100, &mut devices);
    assert_eq!(&machine.work_stack.data[0..2], &[0x20, 0x10]);
    assert_eq!(devices.0[0x10], 0x20);

    let mut machine = machine_from_source("#abcd #10 DEO2");
    machine.execute_vector(0x100, &mut devices);
    assert_eq!(&devices.0[0x10..=0x11], &[0xab, 0xcd])
}

#[test]
fn test_add() {
    assert_work_stack_state("#1a #2e ADD", &[0x48]);
    assert_work_stack_state("#02 #5d ADDk", &[0x02, 0x5d, 0x5f]);
    assert_work_stack_state("#0001 #0002 ADD2", &[0x00, 0x03]);
}

#[test]
fn test_sub() {
    assert_work_stack_state("#2e #1a SUB", &[0x14]);
    assert_work_stack_state("#2e #1a SUBk", &[0x2e, 0x1a, 0x14]);
    assert_work_stack_state("#0002 #0001 SUB2", &[0x00, 0x01]);
}

#[test]
fn test_mul() {
    assert_work_stack_state("#2e #1a MUL", &[0x2eu8.wrapping_mul(0x1a)]);
    assert_work_stack_state("#2e #1a MULk", &[0x2e, 0x1a, 0x2eu8.wrapping_mul(0x1a)]);
    assert_work_stack_state("#0002 #0001 MUL2", &[0x00, 0x02]);
}

#[test]
fn test_div() {
    assert_work_stack_state("#10 #02 DIV", &[0x08]);
    assert_work_stack_state("#10 #03 DIVk", &[0x10, 0x03, 0x05]);
    assert_work_stack_state("#0010 #0000 DIV2", &[0x00, 0x00]);
}

#[test]
fn test_and() {
    assert_work_stack_state("#11 #03 AND", &[0x01]);
    assert_work_stack_state("#12 #03 ANDk", &[0x12, 0x03, 0x02]);
    assert_work_stack_state("#0010 #1010 AND2", &[0x00, 0x10]);
}

#[test]
fn test_ora() {
    assert_work_stack_state("#11 #03 ORA", &[0x13]);
    assert_work_stack_state("#12 #03 ORAk", &[0x12, 0x03, 0x13]);
    assert_work_stack_state("#0010 #1010 ORA2", &[0x10, 0x10]);
}

#[test]
fn test_eor() {
    assert_work_stack_state("#11 #03 EOR", &[0x12]);
    assert_work_stack_state("#12 #03 EORk", &[0x12, 0x03, 0x11]);
    assert_work_stack_state("#0010 #1010 EOR2", &[0x10, 0x00]);
}

#[test]
fn test_sft() {
    assert_work_stack_state("#34 #10 SFT", &[0x68]);
    assert_work_stack_state("#34 #01 SFT", &[0x1a]);
    assert_work_stack_state("#34 #33 SFTk", &[0x34, 0x33, 0x30]);
    assert_work_stack_state("#1248 #34 SFTk2", &[0x12, 0x48, 0x34, 0x09, 0x20]);
}

#[test]
fn test_result_six() {
    assert_work_stack_state("#01 DUP ADD #03 MUL ( result: 06 )", &[0x06]);
}
