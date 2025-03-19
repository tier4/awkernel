# Awkernel

Awkernel is a safe and realtime operating system.
It can execute async/await applications in kernel space safely.

## Progress

- [x] Zero-copy communications
  - [x] Publish and subscribe
  - [x] Service
  - [x] Action
- [x] Channels
  - [x] Bounded channel
  - [x] Unbounded channel
  - [x] Session-type based channel
- [x] Memory space isolation
- [x] Timer interrupts
  - [x] AArch64
  - [x] x86_64
- [x] Interrupt Controllers
  - [x] AArch64
    - [x] Raspberry Pi 3
    - [x] GICv2
    - [x] GICv3
  - [x] x86_64
    - [x] xAPIC
    - [x] x2APIC
- [ ] Frame buffer
  - [ ] AArch64 virt
  - [x] Raspberry Pi 3 and 4
  - [x] x86_64
- [ ] Diagnostics
- [ ] Measurement
- [ ] Power Management
  - [ ] Shutdown
  - [ ] Reboot
- [ ] Schedulers
  - [x] FIFO scheduler
  - [x] Round robin scheduler
  - [ ] Priority Based Round robin scheduler
  - [ ] EDF scheduler
  - [ ] DAG scheduler
- [ ] Memory allocators
  - [x] O(1) memory allocator
  - [x] DMA pool
  - [ ] NUMA aware memory allocator
- [ ] DVFS
  - [ ] AArch64
  - [ ] x86_64
- [ ] PCIe
  - [ ] MSI
    - [x] x86_64 xAPIC and x2APIC
    - [ ] AArch64 GICv3
  - [ ] MSI-X
    - [x] x86_64 xAPIC and x2APIC
    - [ ] AArch64 GICv3
- Network controllers
  - [x] Intel Gb Ethernet Controller (e1000 Series)
  - [ ] Intel 2.5Gb Ethernet Controller (I225/I226 series)
  - [x] Intel 10Gb Ethernet Controller (X520 Series)
  - [ ] Mellanox ConnectX-5 series
  - [x] genet for Raspberry Pi
- Networking
  - [x] IPv4
  - [ ] IPv6
  - [x] UDP
  - [x] TCP
  - [ ] VLAN
  - [x] IP multicast
  - [ ] Offloading
    - [ ] TSO
    - [ ] IPv4 header checksum
    - [x] UDP checksum
    - [ ] TCP checksum
    - [ ] VLAN hardware tagging
- [ ] XHCI
- [ ] Block devices
  - [ ] NVMe
  - [ ] AHCI
- [ ] File systems
  - [ ] FAT32
  - [ ] Journaling file system

## Dependencies


### Compiler Tools

```text
$ sudo apt install clang qemu-system-arm qemu-system-x86 qemu-system-misc python3-pyelftools
$ rustup toolchain install nightly-2025-02-27
$ rustup default nightly-2025-02-27
$ rustup component add rust-src llvm-tools-preview
$ rustup target add x86_64-unknown-none aarch64-unknown-none riscv64gc-unknown-none-elf
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

Debug build.

```text
$ make x86_64
```

Release build.

```text
$ make x86_64 RELEASE=1
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

Release build.
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
  - 8N1: eight data bits, no parity, one stop bit
  - Speed: 115200

---

## RISC-V (64bit, Qemu)

### Compile

Debug build.

```text
$ make riscv64
```

Release build.

```text
$ make riscv64 RELEASE=1
```

### Boot

```text
$ make qemu-riscv64
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

## Verification

[Verification Result](./VERIFICATION.md)
