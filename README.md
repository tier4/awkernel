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
  - [ ] Round robin scheduling
  - [ ] DAG scheduling
- [ ] Multikernel
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
$ make raspi  BSP=raspi4 RELEASE=1
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
