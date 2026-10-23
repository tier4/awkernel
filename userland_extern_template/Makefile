ifeq ($(RELEASE), 1)
  OPT = --release
  BUILD = release
else
  BUILD = debug
endif

RUSTC_MISC_ARGS = -C panic=unwind

# RUSTFLAGS is set explicitly so rustflags inherited from parent
# .cargo/config.toml files do not leak into the build.
RUSTV = $(shell sed -n 's/^channel *= *"\(.*\)"/\1/p' rust-toolchain.toml)

all: x86_64 riscv32 riscv64

check: check_x86_64 check_riscv32 check_riscv64

clippy:
	cargo +$(RUSTV) clippy_x86
	cargo +$(RUSTV) clippy_rv32
	cargo +$(RUSTV) clippy_rv64

cargo: kernel-x86_64.elf

FORCE:

# x86_64

# Debug builds enable the `debug` feature, as in the root Makefile.
ifneq ($(RELEASE), 1)
  X86_OPT = --features debug
endif

x86_64: x86_64_uefi.img

check_x86_64: FORCE
	cargo +$(RUSTV) check_x86

kernel-x86_64.elf: FORCE
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +$(RUSTV) x86 $(OPT) $(X86_OPT)
	cp target/x86_64-kernel/$(BUILD)/awkernel $@
	python3 scripts/embed_debug_info.py $@

# The boot-disk tool is installed once into target/x86bootdisk.
# Override the source with X86BOOTDISK_SRC="--git <url>"; `make clean-tool` reinstalls it.
X86BOOTDISK_SRC ?= --path $(abspath ../x86bootdisk)
X86BOOTDISK = $(CURDIR)/target/x86bootdisk/bin/x86bootdisk

$(X86BOOTDISK):
	# Install from a neutral dir so the kernel target and build-std in .cargo/config.toml do not apply to this host tool.
	cd / && RUSTUP_TOOLCHAIN=$(RUSTV) cargo install $(X86BOOTDISK_SRC) --root $(CURDIR)/target/x86bootdisk --no-default-features --features uefi

x86_64_uefi.img: kernel-x86_64.elf | $(X86BOOTDISK)
	$(X86BOOTDISK) --kernel $< --output $@ --pxe x86_64_uefi_pxe_boot --boot-type uefi

OVMF_PATH := $(CURDIR)/target/ovmf/x64

QEMU_X86_ARGS= -drive if=pflash,format=raw,readonly=on,file=${OVMF_PATH}/code.fd
QEMU_X86_ARGS+= -drive if=pflash,format=raw,file=${OVMF_PATH}/vars_qemu.fd
QEMU_X86_ARGS+= -drive format=raw,file=x86_64_uefi.img
QEMU_X86_ARGS+= -machine q35
QEMU_X86_ARGS+= -device qemu-xhci,id=xhci
QEMU_X86_ARGS+= -serial stdio -smp 4 -monitor telnet::5556,server,nowait
QEMU_X86_ARGS+= -m 4G -smp cpus=16
QEMU_X86_ARGS+= -object memory-backend-ram,size=1G,id=m0
QEMU_X86_ARGS+= -object memory-backend-ram,size=1G,id=m1
QEMU_X86_ARGS+= -object memory-backend-ram,size=1G,id=m2
QEMU_X86_ARGS+= -object memory-backend-ram,size=1G,id=m3
QEMU_X86_ARGS+= -numa node,memdev=m0,cpus=0-3,nodeid=0
QEMU_X86_ARGS+= -numa node,memdev=m1,cpus=4-7,nodeid=1
QEMU_X86_ARGS+= -numa node,memdev=m2,cpus=8-11,nodeid=2
QEMU_X86_ARGS+= -numa node,memdev=m3,cpus=12-15,nodeid=3

QEMU_X86_NET_ARGS=$(QEMU_X86_ARGS)
QEMU_X86_NET_ARGS+= -netdev user,id=net0,hostfwd=udp::4445-:2000
QEMU_X86_NET_ARGS+= -device e1000e,netdev=net0,mac=12:34:56:11:22:33
QEMU_X86_NET_ARGS+= -object filter-dump,id=net0,netdev=net0,file=packets_net0.pcap
QEMU_X86_NET_ARGS+= -netdev user,id=net1,hostfwd=udp::4446-:2001
QEMU_X86_NET_ARGS+= -device virtio-net-pci,netdev=net1,mac=12:34:56:11:22:34,disable-legacy=on,disable-modern=off,speed=1000,duplex=full
QEMU_X86_NET_ARGS+= -object filter-dump,id=net1,netdev=net1,file=packets_net1.pcap

qemu-x86_64-net:
	cp ${OVMF_PATH}/vars.fd ${OVMF_PATH}/vars_qemu.fd
	qemu-system-x86_64 $(QEMU_X86_NET_ARGS)

qemu-x86_64:
	cp ${OVMF_PATH}/vars.fd ${OVMF_PATH}/vars_qemu.fd
	qemu-system-x86_64 $(QEMU_X86_ARGS)

debug-x86_64:
	cp ${OVMF_PATH}/vars.fd ${OVMF_PATH}/vars_qemu.fd
	qemu-system-x86_64 $(QEMU_X86_ARGS) -s -S

qemu-x86_64-nographic:
	cp ${OVMF_PATH}/vars.fd ${OVMF_PATH}/vars_qemu.fd
	qemu-system-x86_64 $(QEMU_X86_ARGS) -nographic

# riscv32

riscv32:
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +$(RUSTV) rv32 $(OPT)

check_riscv32: FORCE
	cargo +$(RUSTV) check_rv32

qemu-riscv32:
	qemu-system-riscv32 -machine virt -bios none -kernel target/riscv32imac-unknown-none-elf/$(BUILD)/awkernel -m 1G -nographic -smp 4 -monitor telnet::5556,server,nowait

# riscv64

riscv64:
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +$(RUSTV) rv64 $(OPT)

check_riscv64: FORCE
	cargo +$(RUSTV) check_rv64

qemu-riscv64:
	qemu-system-riscv64 -machine virt -bios none -kernel target/riscv64gc-unknown-none-elf/$(BUILD)/awkernel -m 1G -nographic -smp 4 -monitor telnet::5556,server,nowait

# Format

fmt: FORCE
	cargo +$(RUSTV) fmt

# Clean

clean: FORCE
	rm -rf *.elf *.img x86_64_uefi_pxe_boot
	cargo clean

clean-tool: FORCE
	rm -rf target/x86bootdisk

## QEMU Monitor

monitor: FORCE
	telnet localhost 5556

.PHONY: all check clippy cargo x86_64 riscv32 riscv64 qemu-x86_64 qemu-x86_64-net qemu-x86_64-nographic debug-x86_64 qemu-riscv32 qemu-riscv64
