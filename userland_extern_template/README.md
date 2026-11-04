# userland_template

Template for a userland that lives outside the Awkernel workspace and depends
on the `awkernel` kernel crate. One crate supports AArch64, x86_64, riscv32 and riscv64.

- `kernel/build.rs` publishes the architecture's linker script as `awkernel.ld`
  (for AArch64, with the board's load address filled in) and adds it to the
  library search path. The AArch64 startup code is part of the kernel crate.
- `build.rs` here passes `-Tawkernel.ld` to the linker.
- `Cargo.toml` features `x86`, `aarch64_virt`, `raspi`, `raspi5`, `rv32`, `rv64` (selected by the cargo aliases in `.cargo/config.toml`) forward to the matching
  `awkernel` feature; enable exactly one.
- `targets/x86_64-kernel.json` and `targets/aarch64-kernel.json` are the kernel targets; riscv uses the
  built-in `riscv32imac`/`riscv64gc` bare-metal targets.
- `src/main.rs` marks its entry point with `#[awkernel::main]`.
- `scripts/embed_debug_info.py` is used for x86_64 builds (needs `pyelftools`).

## Build

The interface mirrors the top-level `Makefile` (`RELEASE=1` for release):

```sh
make                    # aarch64, x86_64, riscv32 and riscv64
make aarch64            # kernel8.img for BSP=aarch64_virt (default), raspi3, raspi4 or raspi5
make qemu-aarch64-virt  # run kernel8.img (BSP=aarch64_virt)
make x86_64             # kernel-x86_64.elf, x86_64_uefi.img, x86_64_uefi_pxe_boot/
make riscv64            # or riscv32
make check clippy fmt   # also check_x86_64, check_riscv32, check_riscv64
make qemu-x86_64        # run the image built by `make x86_64` (does not rebuild); also qemu-x86_64-net, qemu-x86_64-nographic, debug-x86_64
make qemu-riscv64       # or qemu-riscv32; run the ELF built by `make riscv64`
make clean              # clean-tool also removes the installed x86bootdisk
```

`kernel/build.rs` assembles `mpboot.S` for x86_64; it uses `x86_64-elf-gcc` if
installed, else `gcc` (override with `CROSS_COMPILE`).

The x86_64 image is made by the `x86bootdisk` tool, installed once into
`target/x86bootdisk` with `cargo install`. Its source defaults to
`../x86bootdisk`; override with `X86BOOTDISK_SRC="--git <url>"`.
