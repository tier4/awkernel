//! Publishes the linker script of the selected architecture as `awkernel.ld`.
//!
//! The script is copied to `OUT_DIR`, which is added to the native library
//! search path. Cargo forwards that path to the final link of every crate that
//! depends on `awkernel`, so a userland crate only has to pass
//! `-Tawkernel.ld`, e.g. with `println!("cargo:rustc-link-arg-bins=-Tawkernel.ld")`
//! in its own `build.rs`.
//!
//! The AArch64 script is a template: `#INITADDR#` is replaced by the load
//! address of the selected board (`raspi`, `raspi5` or `aarch64_virt`), or by
//! the `INITADDR` environment variable if no board is selected.
//! Its startup code (`boot.S`) is assembled by `global_asm!`.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

fn has_feature(name: &str) -> bool {
    env::var_os(format!("CARGO_FEATURE_{name}")).is_some()
}

fn run_command(cmd: &mut Command) {
    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("failed to run {cmd:?}: {e}"));
    assert!(status.success(), "{cmd:?} failed");
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=ld");

    if has_feature("AARCH64") {
        aarch64();
    } else if has_feature("X86") {
        x86_64();
    } else if has_feature("RV32") {
        riscv32();
    } else if has_feature("RV64") {
        riscv64();
    }
}

fn x86_64() {
    println!("cargo:rerun-if-env-changed=CROSS_COMPILE");

    build_x86_64_mpboot();
    publish_linker_script("x86_64-link.lds", None);
}

fn aarch64() {
    println!("cargo:rerun-if-env-changed=INITADDR");

    // The script is a template that needs the load address of the board.
    // Without a board feature, it is taken from the `INITADDR` environment variable.
    let init_addr = if has_feature("AARCH64_VIRT") {
        "0x40080000".to_string()
    } else if has_feature("RASPI") || has_feature("RASPI5") {
        "0x80000".to_string()
    } else if let Ok(addr) = env::var("INITADDR") {
        addr
    } else {
        // Without a board or `INITADDR` (e.g. a plain `cargo check`), no script is published.
        return;
    };

    publish_linker_script("aarch64-link.lds", Some(("#INITADDR#", &init_addr)));
}

fn riscv32() {
    publish_linker_script("rv32-link.lds", None);
}

fn riscv64() {
    publish_linker_script("rv64-link.lds", None);
}

/// Copies `ld/<script>` to `OUT_DIR/awkernel.ld`, applying `replace` (placeholder, value)
/// if given, and adds `OUT_DIR` to the library search path.
fn publish_linker_script(script: &str, replace: Option<(&str, &str)>) {
    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is not set"));
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is not set"));

    let mut ld = fs::read_to_string(manifest_dir.join("ld").join(script))
        .expect("failed to read the linker script");

    if let Some((placeholder, value)) = replace {
        ld = ld.replace(placeholder, value);
    }

    fs::write(out_dir.join("awkernel.ld"), ld).expect("failed to write the linker script");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
}

/// Builds the real-mode trampoline of the non-primary CPUs as `OUT_DIR/mpboot.img`.
///
/// It mixes 16/32/64-bit code and needs a GNU 32-bit ELF `gcc` and `ld`.
/// Set `CROSS_COMPILE` (e.g. `x86_64-elf-`) to choose the toolchain explicitly.
/// Otherwise `x86_64-elf-` is used if installed (e.g. macOS), else the native one.
fn build_x86_64_mpboot() {
    println!("cargo:rerun-if-changed=asm/x86/mpboot.S");

    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is not set"));
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is not set"));
    let prefix = env::var("CROSS_COMPILE").unwrap_or_else(|_| detect_cross_x86_64_prefix());

    let src = manifest_dir.join("asm/x86/mpboot.S");
    let obj = out_dir.join("mpboot.o");
    let elf = out_dir.join("mpboot.elf");
    let img = out_dir.join("mpboot.img");

    run_command(
        Command::new(format!("{prefix}gcc"))
            .args(["-m32", "-fno-pie", "-nostdlib", "-c"])
            .arg(&src)
            .arg("-o")
            .arg(&obj),
    );

    // See kernel::arch::x86_64::kernel_main::NON_PRIMARY_START
    run_command(
        Command::new(format!("{prefix}ld"))
            .args(["-m", "elf_i386", "-N", "-e", "_start_cpu", "-Ttext", "0"])
            .arg(&obj)
            .arg("-o")
            .arg(&elf),
    );

    run_command(
        Command::new(format!("{prefix}objcopy"))
            .args(["-O", "binary"])
            .arg(&elf)
            .arg(&img),
    );

    assert!(Path::new(&img).exists(), "mpboot.img was not generated");
}

fn detect_cross_x86_64_prefix() -> String {
    let cross = "x86_64-elf-";
    let found = Command::new(format!("{cross}gcc"))
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());

    if found {
        cross.to_string()
    } else {
        String::new()
    }
}
