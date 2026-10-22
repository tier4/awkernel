//! Publishes the linker script of the selected architecture as `awkernel.ld`.
//!
//! The script is copied to `OUT_DIR`, which is added to the native library
//! search path. Cargo forwards that path to the final link of every crate that
//! depends on `awkernel`, so a userland crate only has to pass
//! `-Tawkernel.ld`, e.g. with `println!("cargo:rustc-link-arg-bins=-Tawkernel.ld")`
//! in its own `build.rs`.
//!
//! AArch64 is not covered yet: its script is a template (`#INITADDR#`) and it
//! also needs `boot.S` assembled and linked.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=ld");
    println!("cargo:rerun-if-env-changed=CROSS_COMPILE");

    if env::var_os("CARGO_FEATURE_X86").is_some() {
        build_x86_64_mpboot();
    }

    let script = if env::var_os("CARGO_FEATURE_X86").is_some() {
        "x86_64-link.lds"
    } else if env::var_os("CARGO_FEATURE_RV32").is_some() {
        "rv32-link.lds"
    } else if env::var_os("CARGO_FEATURE_RV64").is_some() {
        "rv64-link.lds"
    } else {
        return;
    };

    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is not set"));
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is not set"));

    fs::copy(
        manifest_dir.join("ld").join(script),
        out_dir.join("awkernel.ld"),
    )
    .expect("failed to copy the linker script");

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
    let prefix = env::var("CROSS_COMPILE").unwrap_or_else(|_| detect_prefix());

    let src = manifest_dir.join("asm/x86/mpboot.S");
    let obj = out_dir.join("mpboot.o");
    let elf = out_dir.join("mpboot.elf");
    let img = out_dir.join("mpboot.img");

    run(Command::new(format!("{prefix}gcc"))
        .args(["-m32", "-fno-pie", "-nostdlib", "-c"])
        .arg(&src)
        .arg("-o")
        .arg(&obj));

    // See kernel::arch::x86_64::kernel_main::NON_PRIMARY_START
    run(Command::new(format!("{prefix}ld"))
        .args(["-m", "elf_i386", "-N", "-e", "_start_cpu", "-Ttext", "0"])
        .arg(&obj)
        .arg("-o")
        .arg(&elf));

    run(Command::new(format!("{prefix}objcopy"))
        .args(["-O", "binary"])
        .arg(&elf)
        .arg(&img));

    assert!(Path::new(&img).exists(), "mpboot.img was not generated");
}

fn detect_prefix() -> String {
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

fn run(cmd: &mut Command) {
    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("failed to run {cmd:?}: {e} (is CROSS_COMPILE set?)"));
    assert!(status.success(), "{cmd:?} failed");
}
