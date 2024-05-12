use std::{
    borrow::BorrowMut,
    collections::VecDeque,
    sync::{Arc, Mutex},
};

use baryuxn::{
    bus::UxnDeviceBus,
    machine::{InactiveUxnVector, UxnMachine, UxnVector},
    UxnArrayRom,
};
use chrono::prelude::*;
use sdl2::{event::Event, keyboard::Keycode, pixels::Color, render::WindowCanvas, Sdl};

/// The screen on which Uxn will draw.

/// Defines how the Uxn stack machine will interact with SDL peripherals.
struct VarvaraSdlDeviceBus {
    storage: [u8; 0x100],
    canvas: WindowCanvas,

    current_x: u16,
    current_y: u16,
    current_address: u16,
}
impl VarvaraSdlDeviceBus {
    pub fn new(context: &mut Sdl, initial_window_width: u32, initial_window_height: u32) -> Self {
        let video = context.video().unwrap();

        let window = video
            .window("baryuxn", initial_window_width, initial_window_height)
            .position_centered()
            .build()
            .unwrap();
        let mut canvas = window.into_canvas().build().unwrap();

        canvas.set_draw_color(Color::RGB(32, 0, 32));
        canvas.clear();
        canvas.present();

        Self {
            storage: [0; 0x100],
            canvas,
            current_x: 0,
            current_y: 0,
            current_address: 0,
        }
    }

    pub fn draw(&mut self) {
        self.canvas.clear();
        self.canvas.present();
    }
}
impl<T> UxnDeviceBus<T> for VarvaraSdlDeviceBus {
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
            0x20 => match port {
                // Screen
                0x02 => ((self.canvas.window().drawable_size().0 >> 8) & 0x0f) as u8,
                0x03 => ((self.canvas.window().drawable_size().0) & 0x0f) as u8,
                0x04 => ((self.canvas.window().drawable_size().1 >> 8) & 0x0f) as u8,
                0x05 => ((self.canvas.window().drawable_size().1) & 0x0f) as u8,
                0x08 => (self.current_x >> 8) as u8,
                0x09 => (self.current_x & 0x0f) as u8,
                0x0a => (self.current_y >> 8) as u8,
                0x0b => (self.current_y & 0x0f) as u8,
                0x0c => (self.current_address >> 8) as u8,
                0x0d => (self.current_address & 0x0f) as u8,
                _ => self.storage[address as usize],
            },
            0x30..=0x60 => todo!(), // Audio
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
                0x0e if byte != 0 => {
                    // TODO: maybe check the byte and add more functionnality depending
                    // on its value?
                    log::debug!(
                        "WST ( {:?} )\nRST ( {:?} )",
                        machine.work_stack,
                        machine.return_stack
                    );
                }
                0x0f if byte != 0 => {
                    todo!("should quit gracefully")
                }
                _ => {}
            },
            0x10 => match port {
                // Console
                0x08 => print!("{}", byte as char),
                0x09 => eprint!("{}", byte as char),
                _ => {}
            },
            0x20 => todo!(),        // Screen
            0x30..=0x60 => todo!(), // Audio
            0x80 => todo!(),        // Controller
            0x90 => todo!(),        // Mouse
            0xa0..=0xb0 => todo!(), // File
            _ => {}
        }
    }
}

pub fn run(rom: [u8; 0x10000]) {
    let mut context = sdl2::init().unwrap();

    let mut uxn_machine = UxnMachine::new(UxnArrayRom { data: rom });
    let mut varvara_devices = VarvaraSdlDeviceBus::new(&mut context, 800, 600);
    let mut active_vector: Option<UxnVector<'_, UxnArrayRom, VarvaraSdlDeviceBus>> = None;
    let mut vector_queue = VecDeque::from([InactiveUxnVector(0x100)]);

    let mut event_pump = context.event_pump().unwrap();
    'event_loop: loop {
        let varavara_pointer = core::ptr::from_mut(&mut varvara_devices);
        // Execute one instruction
        if let Some(inactive_vector) = vector_queue.pop_back() {
            if let Some(active_vector) = active_vector.take() {
                vector_queue.push_front(active_vector.make_inactive());
            }
            active_vector = Some(inactive_vector.make_active(&mut uxn_machine, unsafe {
                varavara_pointer.as_mut().unwrap()
            }))
        }

        if let Some(mut active_vector) = active_vector.take() {
            if let Some(instruction) = active_vector.next() {
                log::info!("executed {instruction:#0x}");
            }
            vector_queue.push_front(active_vector.make_inactive())
        }

        for event in event_pump.poll_iter() {
            match event {
                Event::Quit { .. }
                | Event::KeyDown {
                    keycode: Some(Keycode::Escape),
                    ..
                } => break 'event_loop,
                _ => {}
            }
        }

        varvara_devices.draw()
    }
}
