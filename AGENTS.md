# Repository Guidelines

## Project Structure & Module Organization
This repository is a Rust workspace (`Cargo.toml`) with these primary areas:

- `kernel/`: core OS kernel crate.
- `awkernel_lib/`, `awkernel_async_lib/`, `awkernel_drivers/`: shared kernel/runtime infrastructure.
- `awkernel_aarch64/`, `x86bootdisk/`: architecture/platform support helpers.
- `userland/`: user-space library and app support.
- `applications/`: runnable samples/tests (`applications/tests/*`) and app crates.
- `smoltcp/`: network stack crate used by kernel/user code.
- `mdbook/`: documentation source; `docs/` stores generated docs output.
- `specification/`: design and implementation notes.
- `docker/`, `scripts/`, `targets/`, `misc/`: tooling, build config, boot artifacts, and platform files.

## Build, Test, and Development Commands
- `make x86_64 [RELEASE=1]`: build x86_64 kernel image.
- `make aarch64 BSP=<raspi3|raspi4|raspi5|aarch64_virt> [RELEASE=1]`: build AArch64 targets.
- `make riscv32` / `make riscv64`: build RISC-V targets.
- `make qemu-x86_64`, `make qemu-aarch64-virt`, `make qemu-raspi3`: boot in QEMU.
- `make check`: run check across kernel targets and std crates.
- `make clippy`: run lints for major targets.
- `make test`: run `test_awkernel_lib`, `test_awkernel_async_lib`, `test_awkernel_drivers`, `test_smoltcp`, `test_rd_gen_to_dags`.
- `make docs`: build mdBook docs.
- `make fmt`: run `cargo fmt`.
- Direct aliases are in `.cargo/config.toml` (examples: `cargo +nightly-2026-06-13 test_awkernel_lib`, `cargo +nightly-2026-06-13 x86`, `cargo +nightly-2026-06-13 doc_x86`).

## Coding Style & Naming Conventions
- Rust 2021 edition, default rustfmt formatting (`cargo fmt`).
- Use 4-space indentation and standard Rust naming:
  - crates, modules, functions: `snake_case`.
  - types/traits: `CamelCase`.
  - test functions: `test_*`.
- Prefer small, explicit feature-gated modules; avoid broad default features.
- Keep architecture-specific code separated by crate and feature flags (`x86`, `aarch64`, `rv32`, `rv64`, `std`).

## Testing Guidelines
- Unit tests are in `mod tests` blocks under crate source and can be run per-package through cargo aliases (e.g., `cargo +nightly-2026-06-13 test_awkernel_lib`).
- Integration-style workload tests are under `applications/tests/*`, typically invoked through the general `make test` suite.
- For behavior validation requiring emulation, reproduce with matching QEMU target command and board (`qemu-...` targets).
- Use `cargo +nightly-2026-06-13 clippy_x86` / `clippy_rv64` style aliases for target-specific linting.

## Commit & Pull Request Guidelines
- Use Conventional Commit style observed in history: `type(scope): short summary` (examples: `feat(async): ...`, `fix(task): ...`, `test(task): ...`).
- Keep each commit focused to one logical change.
- PRs should include:
  - target architecture and commands run (`make`, `cargo`, QEMU target),
  - rationale for API/behavior changes,
  - test commands and results.
- Link related issues when applicable and call out platform impact (`x86_64`, `aarch64`, `riscv32`, `riscv64`).

## Security & Environment Notes
- Repository uses nightly toolchain; ensure `rustup toolchain install nightly-2026-06-13` and target support are in place before builds.
- x86 UEFI QEMU flows require `OVMF_PATH` to point at valid `code.fd` and `vars.fd` locations.
