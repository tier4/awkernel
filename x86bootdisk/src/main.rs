use std::path::Path;

use bootloader::{BiosBoot, UefiBoot};
use clap::Parser;

#[derive(Debug, clap::ValueEnum, Clone)]
enum BootType {
    Uefi,
    Bios,
}

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to kernel.
    #[arg(short, long)]
    kernel: String,

    /// Output.
    #[arg(short, long)]
    output: String,

    /// UEFI or BIOS.
    #[arg(value_enum, long, default_value_t = BootType::Bios)]
    boot_type: BootType,
}

fn main() {
    let args = Args::parse();

    let kernel_path = Path::new(&args.kernel);
    let output_path = Path::new(&args.output);

    match args.boot_type {
        BootType::Uefi => {
            UefiBoot::new(kernel_path)
                .create_disk_image(output_path)
                .unwrap();

            let ovmf_path = ovmf_prebuilt::ovmf_pure_efi();
            println!("Prebuild OVMF binaries: {}", ovmf_path.display());
            println!(
                "\nRun:\nqemu-system-x86_64 -bios {} -drive format=raw,file={} -serial stdio",
                ovmf_path.display(),
                output_path.display()
            )
        }
        BootType::Bios => {
            BiosBoot::new(kernel_path)
                .create_disk_image(output_path)
                .unwrap();
            println!(
                "\nRun:\nqemu-system-x86_64 -drive format=raw,file={} -serial stdio",
                output_path.display()
            )
        }
    }
}
