# userland_template

Template for a userland that lives outside the Awkernel workspace and depends
on the `awkernel` kernel crate. One crate supports x86_64, riscv32 and riscv64
(AArch64 is not supported yet: the kernel does not publish its linker script
and `boot.S` for out-of-tree crates).

- `kernel/build.rs` copies the architecture's linker script to `OUT_DIR` as
  `awkernel.ld` and adds it to the library search path.
- `build.rs` here passes `-Tawkernel.ld` to the linker.
- `Cargo.toml` features `x86`, `rv32`, `rv64` (selected by the cargo aliases in `.cargo/config.toml`) forward to the matching
  `awkernel` feature; enable exactly one.
- `targets/x86_64-kernel.json` is the x86_64 kernel target; riscv uses the
  built-in `riscv32imac`/`riscv64gc` bare-metal targets.
- `src/main.rs` marks its entry point with `#[awkernel::main]`.
- `scripts/embed_debug_info.py` is used for x86_64 builds (needs `pyelftools`).

## Build

The interface mirrors the top-level `Makefile` (`RELEASE=1` for release):

```sh
make                    # x86_64, riscv32 and riscv64
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
