# Awkernel

Awkernel is a safe and realtime operating system.
It can execute async/await applications in kernel space safely.

## Dependencies

### Compiler Tools

```text
$ sudo apt install clang qemu-system-arm qemu-system-x86 qemu-system-misc python3-pyelftools
$ rustup toolchain install nightly-2025-11-16
$ rustup default nightly-2025-11-16
$ rustup component add rust-src llvm-tools-preview
$ rustup target add x86_64-unknown-none aarch64-unknown-none riscv64gc-unknown-none-elf riscv32imac-unknown-none-elf
```

### Documentation Tools

```text
$ cargo install cargo-binutils
$ curl -L --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/cargo-bins/cargo-binstall/main/install-from-binstall-release.sh | bash
$ cargo binstall mdbook
$ cargo binstall mdbook-mermaid
```

## Crates

- [kernel](./kernel/)
  - boot code
  - initialization
    - virtual memory
    - heap memory
    - stack memory
    - devices (UART, etc)
- [awkernel_lib](./awkernel_lib/)
  - library used by both [kernel](./kernel/) and [awkernel_async_lib](./awkernel_async_lib/)
- [awkernel_async_lib](./awkernel_async_lib/)
  - asynchronous library for no_std
- [awkernel_async_lib_verified](./awkernel_async_lib_verified/)
  - verified library for awkernel_async_lib
  - pure Rust (no dependencies on external functions and no inline assembly)
- [awkernel_futures_macro](./awkernel_futures_macro/)
- [awkernel_drivers](./awkernel_drivers/)
- [awkernel_aarch64](./awkernel_aarch64/)
- [userland](./userland/)
- applications
  - [awkernel_shell](./applications/awkernel_shell/)

```mermaid
graph TD;
    awkernel_async_lib-->awkernel_async_lib_verified;
    awkernel_async_lib-->awkernel_futures_macro;
    awkernel_lib-->awkernel_aarch64;
    awkernel_async_lib-->awkernel_lib;
    awkernel_lib-->awkernel_sync;
    userland-->awkernel_async_lib;
    kernel-->awkernel_lib;
    kernel-->awkernel_async_lib;
    kernel-->awkernel_aarch64;
    kernel-->awkernel_drivers;
    awkernel_drivers-->awkernel_lib;
    kernel-->userland;
```

Applications can use `awkernel_async_lib`, `awkernel_lib`, and `awkernel_drivers`.

---

## Documents

```text
$ make docs
$ ls docs/index.html
```

### Raspi

```text
$ cargo doc_raspi
$ ls target/aarch64-kernel/doc/awkernel/index.html
$ ls target/aarch64-kernel/doc/awkernel_lib/index.html
etc
```

### AArch64 Qemu Virt

```text
$ cargo doc_aarch64_virt
$ ls target/aarch64-kernel/doc/awkernel/index.html
$ ls target/aarch64-kernel/doc/awkernel_lib/index.html
etc
```

### x86_64

```text
$ make kernel/asm/x86
$ cargo doc_x86
$ ls target/x86_64-kernel/doc/awkernel/index.html
$ ls target/aarch64-kernel/doc/awkernel_lib/index.html
etc
```

---

## x86_64

### Compile

Release build (recommended).

```text
$ make x86_64 RELEASE=1
```

Debug build.

```text
$ make x86_64
```

### Boot

Qemu 8.x or later is required.
Qemu 6.x is not supported.

```text
$ make qemu-x86_64
```

### GDB

```text
$ make debug-x86_64
$ make gdb-x86_64
```

---

## AArch64 Qemu Virt

### Compile

Release build (recommended).

```text
$ make aarch64 BSP=aarch64_virt RELEASE=1
```

Debug build.

```text
$ make aarch64 BSP=aarch64_virt
```

### Boot

```text
$ make qemu-aarch64-virt
```

### GDB

```text
$ make debug-aarch64_virt
$ make gdb-aarch64_virt
```

---

## Raspberry Pi 3 (AArch64, Qemu) or Raspberry Pi Zero 2 W

### Compile

Release build (recommended).
`RELEASE=1` must be used for actual devices.

```text
$ make aarch64 BSP=raspi3 RELEASE=1
```

Debug build.

```text
$ make aarch64 BSP=raspi3
```

### Boot

```text
$ make qemu-raspi3
```

### GDB

```text
$ make debug-raspi3
$ make gdb-raspi3
```

---

## Raspberry Pi 4 (AArch64)

### Compile

Specify `Release=1`.

```text
$ make aarch64 BSP=raspi4 RELEASE=1
```

### Boot

- Serial
  - port: GPIO 14 (Tx) and 15 (Rx)
  - 8N1: eight data bits, no parity, one stop bit
  - Speed: 115200

---

## Raspberry Pi 5 (AArch64)

### Compile

Specify `Release=1`.

```text
$ make aarch64 BSP=raspi5 RELEASE=1
```

### Boot

- Serial
  - port: GPIO 14 (Tx) and 15 (Rx)
  - 8N1: eight data bits, no parity, one stop bit
  - Speed: 115200

---

## RISC-V (64bit, Qemu)

### Compile

Release build (recommended).

```text
$ make riscv64 RELEASE=1
```

Debug build.

```text
$ make riscv64
```

### Boot

```text
$ make qemu-riscv64
```

---

## RISC-V (32bit, Qemu)

### Compile

Release build (recommended).

```text
$ make riscv32 RELEASE=1
```

Debug build.

```text
$ make riscv32
```

### Boot

```text
$ make qemu-riscv32
```

---

## Linux / macOS

### Compile

Debug build.

```text
$ make std
```

Release build.

```text
$ make std RELEASE=1
```

### Boot

Debug build.

```text
$ make run-std
```

Release build.

```text
$ make run-std RELEASE=1
```

## Qemu Monitor

```text
$ make qemu-raspi3
$ telnet localhost 5556
```

---

## Test

Unit tests by using Rust's mechanism can be executed as follows.

```text
$ make test
```

Some mechanisms which use atomic instructions are verified by using [loom](https://github.com/tokio-rs/loom),
and these verifications are executed as follows.
It will takes several minutes.

```text
$ make loom
```

## Publications

[Publications](./PUBLICATIONS.md)

## Specification and Test Results

[Specification and Test Results](./SPEC_TEST.md)
