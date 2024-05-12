use std::{fs::File, io::Read, path::PathBuf};

use baryuxn_sdl2::run;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Arguments {
    rom_file: PathBuf,
}

fn main() {
    let args = Arguments::parse();
    let mut rom = [0; 0x10000];
    File::open(args.rom_file)
        .unwrap()
        .read(&mut rom[0x100..])
        .unwrap();
    run(rom)
}
