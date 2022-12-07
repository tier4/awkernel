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
$ rustup component add rust-src llvm-tools-preview
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
$ make raspi3
```

Release build.

```text
$ make raspi3 RELEASE=1
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
$ make run-x86_64
```

### AArch64

```text
$ make run-raspi3
```

### Linux

```text
$ make run-linux
```

Release build.

```text
$ make run-linux RELEASE=1
```
