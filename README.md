# Autoware Kernel

Autoware kernel is a safe and realtime operating system supporting
isolated zero-copy communications written in Rust.

## Progress

- [x] Zero-copy communication
  - [x] Publish and subscribe
  - [x] Service
  - [x] Action
- [ ] Isolation
  - [x] Memory space isolation
  - [ ] Temporal isolation
- [ ] Scheduling
  - [x] Round robin scheduler
  - [ ] DAG scheduler
- [x] O(1) memory allocator
- [ ] Cokernel
- [ ] TEE
  - [ ] TrustZone

## Dependencies

```text
$ sudo apt install clang qemu-system-arm qemu-system-x86 qemu-system-misc
$ rustup toolchain install nightly
$ rustup default nightly
$ rustup component add rust-src llvm-tools-preview
$ rustup target add x86_64-unknown-none aarch64-unknown-none riscv32imac-unknown-none-elf
$ cargo install cargo-binutils
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
- [awkernel_drivers](./awkernel_drivers/)
- [awkernel_aarch64](./awkernel_aarch64/)
- [userland](./userland/)
- applications
  - [awkernel_shell](./applications/awkernel_shell/)

```mermaid
graph TD;
    awkernel_async_lib-->awkernel_async_lib_verified;
    awkernel_lib-->awkernel_aarch64;
    awkernel_async_lib-->awkernel_lib;
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

## x86_64

### Compile

Debug build.

```text
$ make x86_64
```

Release build.

```text
$ make x86_64 RELEASE=1
```

If you want to use UEFI, make `x86_64_uefi.img` as follows.

```text
$ make x86_64_uefi.img
```

### Boot

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

Debug build.

```text
$ make aarch64 BSP=aarch64_virt
```

Release build.

```text
$ make aarch64 BSP=aarch64_virt RELEASE=1
```

### Boot

```text
$ make qemu-aarch64_virt
```

### GDB

```text
$ make debug-aarch64_virt
$ make gdb-aarch64_virt
```

---

## Raspberry Pi 3 (AArch64, Qemu)

### Compile

Debug build.

```text
$ make aarch64 BSP=raspi3
```

Release build.

```text
$ make aarch64 BSP=raspi3 RELEASE=1
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

Debug build.

```text
$ make aarch64 BSP=raspi4
```

Release build.

```text
$ make aarch64 BSP=raspi4 RELEASE=1
```

### Boot

- Serial
  - port: GPIO 14 (Tx) and 15 (Rx)
  - 8N1: eight data bits, no parity, one stop bit
  - Speed: 115200

---

## RISC-V (32bit)

### Compile

Debug build.

```text
$ make riscv32
```

Release build.

```text
$ make riscv32 RELEASE=1
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
