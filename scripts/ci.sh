#!/bin/sh
# Runs the checks of .github/workflows/rust.yml.
# The environment setup (toolchain, targets, cargo tools) is not done here.
set -eux

export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-nightly-2026-07-20}"

cargo fmt --check

for bsp in aarch64_virt raspi5 raspi4 raspi3; do
    make check_aarch64 BSP="$bsp"
done
make check_x86_64
make check_riscv32
make check_riscv64
make check_std

for t in aarch64_virt raspi raspi5 x86 rv32 rv64 std rd_gen_to_dags; do
    cargo "clippy_$t" -- --deny warnings
done

make udeps

RUSTFLAGS="-D warnings" make test
