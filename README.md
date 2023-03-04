# O4OS: Open Intelligent Vehicle Operating System

Open Intelligent Vehicle Operating System (O4OS) is a safe and realtime operating system supporting
isolated zero-copy communications written in Rust.

- Open = O
- Intelligent Vehicle = IV = 4
- Operating System = OS

## Progress

- [x] Zero-copy communication
  - [x] Publish and subscribe
  - [x] Service
  - [ ] Action
- [ ] Isolation
  - [ ] Memory isolation
  - [ ] Computational isolation
- [ ] Realtime scheduling
  - [x] Round robin scheduling
  - [ ] DAG scheduling
- [x] O(1) memory allocator
- [ ] Cokernel
- [ ] TEE
  - [ ] TrustZone

## Dependencies

```text
$ sudo apt install clang qemu-system-arm qemu-system-x86
$ rustup toolchain install nightly
$ rustup default nightly
$ rustup component add rust-src llvm-tools-preview
$ rustup target add x86_64-unknown-none aarch64-unknown-none-softfloat
$ cargo install cargo-binutils
```

## Compile

### x86_64

Debug build.

```text
$ make x86_64
```

Release build.

```text
$ make x86_64 RELEASE=1
```

### Raspberry Pi 3 (AArch64)

Debug build.

```text
$ make raspi
```

Release build.

```text
$ make raspi RELEASE=1
```

### Raspberry Pi 4 (AArch64)

Debug build.

```text
$ make raspi BSP=raspi4
```

Release build.

```text
$ make raspi BSP=raspi4 RELEASE=1
```

### Linux

```text
$ make linux
```

Release build.

```text
$ make linux RELEASE=1
```

## Boot

### x86\_64

```text
$ make qemu-x86_64
```

### Raspberry Pi 3 (AArch64)

```text
$ make qemu-raspi3
```

### Raspberry Pi 4 (AArch64)

- Serial
  - port: GPIO 14 (Tx) and 15 (Rx)
  - 8N1: eight data bits, no parity, one stop bit
  - Speed: 115200

### Linux

```text
$ make run-linux
```

Release build.

```text
$ make run-linux RELEASE=1
```

## Qemu Monitor

```text
$ make qemu-raspi3
$ telnet localhost 5556
```

## GDB

### Raspberry Pi 3 (AArch64)

```text
$ make debug-raspi3
$ make gdb-raspi3
```

### x86\_64

```text
$ make debug-x86_64
$ make gdb-x86_64
```