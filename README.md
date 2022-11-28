# T4OS: T4 Operating System

T4 Operating System (T4OS) is a safe and realtime operating system supporting
isolated zero-copy communications written in Rust.

## Progress

- [ ] Zero-copy communication
  - [ ] Publish and subscribe
- [ ] Isolation
  - [ ] Memory isolation
  - [ ] Computational isolation
- [ ] Realtime scheduling
  - [ ] DAG scheduling
  - [ ] Multiple times
- [ ] Multikernel
- [ ] TEE
  - [ ] TrustZone

## Compile

```text
$ cargo +nightly x86
```

## Boot

### x86\_64

```text
$ git clone https://github.com/rust-osdev/bootloader.git -b v0.10.13
```

```text
$ cd bootloader
$ cargo builder --kernel-manifest /path/to/t4os/kernel/Cargo.toml --kernel-binary /path/to/t4os/kernel_x86-64.elf
$ qemu-system-x86_64 -drive format=raw,file=./target/x86_64-bootloader/release/boot-bios-kernel_x86-64.img -serial stdio
```

### AArch64

Not yet.
