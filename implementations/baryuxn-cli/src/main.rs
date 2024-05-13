use std::{
    collections::VecDeque,
    fs::File,
    io::{stdout, BufReader, Read, Write},
    path::Path,
    sync::mpsc::TryRecvError,
};

use baryasm::UxnTalAssembler;
use baryuxn::{
    machine::{InactiveUxnVector, UxnMachine},
    UxnArrayRom, UxnDeviceBus,
};
use chrono::{Datelike, Local, Timelike};

/// Defines how the Uxn stack machine will interact with SDL peripherals.
struct CliDeviceBus {
    storage: [u8; 0x100],
    debug: bool,
    should_quit: bool,
}
impl CliDeviceBus {
    pub fn new(debug: bool) -> Self {
        Self {
            storage: [0; 0x100],
            debug,
            should_quit: false,
        }
    }
    pub fn write_character(&mut self, b: u8) -> InactiveUxnVector {
        self.storage[0x12] = b;
        self.storage[0x17] = if b == 0 { 0x04 } else { 0x01 };
        InactiveUxnVector(u16::from_be_bytes([self.storage[0x10], self.storage[0x11]]))
    }
}
impl<T> UxnDeviceBus<T> for CliDeviceBus {
    fn read(&mut self, machine: &mut UxnMachine<T>, address: u8) -> u8 {
        let page = address & 0xf0;
        let port = address & 0x0f;
        match page {
            0x00 => match port {
                // System
                0x04 => machine.work_stack.pointer,
                0x05 => machine.return_stack.pointer,
                _ => self.storage[address as usize],
            },
            0xc0 => {
                // DateTime
                let time = Local::now();
                match port {
                    0x00 => ((time.year() as u16) >> 8) as u8,
                    0x01 => ((time.year() as u16) & 0x00ff) as u8,
                    0x02 => time.month0() as u8,
                    0x03 => time.day0() as u8,
                    0x04 => time.hour() as u8,
                    0x05 => time.minute() as u8,
                    0x06 => time.second() as u8,
                    0x07 => time.weekday() as u8,
                    0x08 => todo!(), // TODO: day of the year
                    0x09 => todo!(), // TODO: day of the year
                    0x0a => todo!(), // TODO: daytime savings
                    _ => self.storage[address as usize],
                }
            }
            _ => self.storage[address as usize],
        }
    }
    fn write(&mut self, machine: &mut UxnMachine<T>, address: u8, byte: u8) {
        let page = address & 0xf0;
        let port = address & 0x0f;
        self.storage[address as usize] = byte;
        // Specific actions
        match page {
            0x00 => match port {
                // System
                0x03 => panic!("Expansions not yet implemented"),
                0x04 => machine.work_stack.pointer = byte,
                0x05 => machine.return_stack.pointer = byte,
                0x0e if byte != 0 && self.debug => {
                    // TODO: maybe check the byte and add more functionnality depending
                    // on its value?
                    println!(
                        "WST ( {:?} )\nRST ( {:?} )",
                        machine.work_stack, machine.return_stack
                    );
                }
                0x0f if byte != 0 => self.should_quit = true,
                _ => {}
            },
            0x10 => match port {
                // Console
                0x08 => {
                    print!("{}", byte as char);
                    stdout().flush().unwrap()
                }
                0x09 => {
                    eprint!("{}", byte as char);
                    stdout().flush().unwrap()
                }
                _ => {}
            },
            0xa0..=0xb0 => {
                todo!("File operations not yet implemented")
            } // File
            _ => {}
        }
    }
}

fn main() {
    // Parse args
    let mut args = std::env::args().skip(1);

    let rom_path;
    let mut debug = false;
    if let Some(arg) = args.next() {
        if arg == "-v" {
            debug = true;
            if let Some(arg) = args.next() {
                rom_path = arg.clone()
            } else {
                println!("expected usage: baryuxn-cli [-v] ROM [args..]");
                return;
            }
        } else {
            rom_path = arg.clone()
        }
    } else {
        println!("expected usage: baryuxn-cli [-v] ROM|TAL [args..]");
        return;
    }

    // Read/compile ROM
    let rom = match Path::new(&rom_path)
        .extension()
        .map(|s| s.to_str().unwrap())
    {
        Some("tal") => UxnTalAssembler::<'_, 0x10000>::new()
            .parse(
                BufReader::new(File::open(rom_path).unwrap())
                    .bytes()
                    .map(|e| e.unwrap()),
            )
            .unwrap(),
        Some("rom") => {
            let mut rom = [0; 0x10000];
            File::open(rom_path)
                .unwrap()
                .read(&mut rom[0x100..])
                .unwrap();
            rom
        }
        _ => {
            println!("Requires either a .rom or .tal file as input");
            return;
        }
    };

    // Create our machine
    let mut devices = CliDeviceBus::new(debug);
    let mut machine = UxnMachine::new(UxnArrayRom { data: rom });

    // Listening to stdin
    let stdin_channel = {
        let (tx, rx) = std::sync::mpsc::channel::<u8>();
        std::thread::spawn(move || loop {
            let mut buffer = [0];
            std::io::stdin().read(&mut buffer).unwrap();
            tx.send(buffer[0]).unwrap()
        });
        rx
    };

    // Evaluate the ROM
    let mut vector_queue = VecDeque::from([InactiveUxnVector(0x100)]);
    // As a means of initialization, the first vector of the program is executed,
    // then arguments passed are parsed
    while !devices.should_quit {
        // Read from stdin and execute vector if there is a character.
        match stdin_channel.try_recv() {
            Ok(b) => {
                let vector = devices.write_character(b);
                machine.execute_vector(vector.0, &mut devices)
            }
            Err(TryRecvError::Empty) => {}
            Err(TryRecvError::Disconnected) => panic!("stdin was closed unexpectedly"),
        }

        let mut vector = if let Some(inactive_vector) = vector_queue.pop_back() {
            inactive_vector.make_active(&mut machine, &mut devices)
        } else {
            continue;
        };

        if let Some(_instruction) = vector.next() {
            vector_queue.push_front(vector.make_inactive())
        }
    }
}
