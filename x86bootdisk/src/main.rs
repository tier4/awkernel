use bootloader::{BiosBoot, UefiBoot};
use clap::Parser;
use ovmf_prebuilt::{Prebuilt, Source};
use std::{fs::File, io::Write, path::Path};

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

    /// Output.
    #[arg(short, long, default_value_t = String::new())]
    pxe: String,

    /// uefi or bios.
    #[arg(value_enum, long, default_value_t = BootType::Bios)]
    boot_type: BootType,
}

fn main() {
    let args = Args::parse();

    let kernel_path = Path::new(&args.kernel);
    let output_path = Path::new(&args.output);
    let pxe_path = Path::new(&args.pxe);

    match args.boot_type {
        BootType::Uefi => {
            let uefi = UefiBoot::new(kernel_path);
            uefi.create_disk_image(output_path).unwrap();
            uefi.create_pxe_tftp_folder(pxe_path).unwrap();

            Prebuilt::fetch(Source::LATEST, "target/ovmf").expect("failed to update prebuilt");

            let ovmf_path = std::fs::canonicalize(Path::new("target/ovmf/x64"))
                .expect("failed to find OVMF binary");

            let dot_ovmfpath = home::home_dir().unwrap().join(".ovfmpath");
            let mut file = File::create(dot_ovmfpath).unwrap();
            file.write_fmt(format_args!("{}", ovmf_path.display()))
                .unwrap();

            println!("Prebuild OVMF binaries: {}", ovmf_path.display());
            println!(
                "\nRun:\nqemu-system-x86_64 -drive if=pflash,format=raw,readonly=on,file={}/code.fd -drive if=pflash,format=raw,file={}/vars.fd -drive format=raw,file={} -serial stdio -monitor telnet::5556,server,nowait -smp 4 -m 512",
                ovmf_path.display(),
                ovmf_path.display(),
                output_path.display()
            )
        }
        BootType::Bios => {
            BiosBoot::new(kernel_path)
                .create_disk_image(output_path)
                .unwrap();
            println!(
                "\nRun:\nqemu-system-x86_64 -drive format=raw,file={} -serial stdio -monitor telnet::5556,server,nowait -smp 4 -m 512",
                output_path.display()
            )
        }
    }
}
