ifndef $(BSP)
	BSP = raspi3
endif

ifeq ($(RELEASE), 1)
	OPT = --release
	BUILD = release
else
	BUILD = debug
endif

ifeq ($(RV), 1)
	OPT += --features runtime_verification
endif

# 2MiB Stack
STACKSIZE = 1024 * 1024 * 2

ifeq ($(BSP),raspi3)
	RUSTC_MISC_ARGS = -C target-cpu=cortex-a53
	INITADDR = 0x80000
	AARCH64_OPT = $(OPT) --features raspi
else ifeq ($(BSP),raspi4)
	RUSTC_MISC_ARGS = -C target-cpu=cortex-a72
	INITADDR = 0x80000
	AARCH64_OPT = $(OPT) --features raspi
else ifeq ($(BSP),raspi5)
	RUSTC_MISC_ARGS = -C target-cpu=cortex-a76
	INITADDR = 0x80000
	AARCH64_OPT = $(OPT) --features raspi5
else ifeq ($(BSP),aarch64_virt)
	RUSTC_MISC_ARGS = -C target-cpu=cortex-a72
	INITADDR = 0x40080000
	AARCH64_OPT = $(OPT) --features aarch64_virt
endif

ASM_FILE_DEP_AARCH64=kernel/asm/aarch64/exception.S
ASM_FILE_AARCH64=kernel/asm/aarch64/boot.S
ASM_OBJ_AARCH64=boot_aarch64.o

X86ASM=kernel/asm/x86

ifndef $(CC)
	CC = clang
endif

ifndef $(LD)
	LD = rust-lld -flavor gnu
	# LD = ld.gold
endif


QEMUPORT=5556

# Link scripts
LINKERDIR=kernel/ld
AARCH64_LD=$(LINKERDIR)/aarch64-link.lds
AARCH64_BSP_LD=$(LINKERDIR)/aarch64-link-bsp.lds
X86_64_LD=$(LINKERDIR)/x86_64-link.lds
RV32_LD=$(LINKERDIR)/rv32-link.lds

RUSTV=nightly-2024-05-08

all: aarch64 x86_64 riscv32 std

check: check_aarch64 check_x86_64 check_std check_riscv32

clippy:
	cargo +$(RUSTV) clippy_x86
	cargo +$(RUSTV) clippy_raspi
	cargo +$(RUSTV) clippy_raspi5
	cargo +$(RUSTV) clippy_aarch64_virt
	cargo +$(RUSTV) clippy_rv32
	cargo +$(RUSTV) clippy_std

cargo: target/aarch64-kernel/$(BUILD)/awkernel kernel-x86_64.elf std

FORCE:

# AArch64
aarch64: kernel8.img

check_aarch64: FORCE
	cargo +$(RUSTV) check_aarch64 $(AARCH64_OPT)

target/aarch64-kernel/$(BUILD)/awkernel: $(ASM_OBJ_AARCH64) $(AARCH64_BSP_LD) FORCE
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +$(RUSTV) aarch64 $(AARCH64_OPT)

kernel8.img: target/aarch64-kernel/$(BUILD)/awkernel
	rust-objcopy -O binary target/aarch64-kernel/$(BUILD)/awkernel $@

$(ASM_OBJ_AARCH64): $(ASM_FILE_AARCH64) $(ASM_FILE_DEP_AARCH64)
	$(CC) --target=aarch64-elf -c $< -o $@ -DSTACKSIZE="$(STACKSIZE)"

$(AARCH64_BSP_LD): $(AARCH64_LD)
	sed "s/#INITADDR#/$(INITADDR)/" $(AARCH64_LD) > $@

QEMU_AARCH64_ARGS= -kernel kernel8.img
QEMU_AARCH64_ARGS+= -serial stdio
QEMU_AARCH64_ARGS+= -monitor telnet::$(QEMUPORT),server,nowait # -d int

## Raspi3

QEMU_RASPI3_ARGS= -m 1024 -M raspi3b -dtb misc/raspi3/bcm2710-rpi-3-b-plus.dtb $(QEMU_AARCH64_ARGS)

qemu-raspi3:
	qemu-system-aarch64 $(QEMU_RASPI3_ARGS)

debug-raspi3:
	qemu-system-aarch64 $(QEMU_RASPI3_ARGS) -s -S

gdb-raspi3:
	gdb-multiarch -x scripts/aarch64-debug.gdb

## Virt

QEMU_AARCH64_VIRT_ARGS= -M virt,gic-version=3 -cpu cortex-a72 $(QEMU_AARCH64_ARGS)
QEMU_AARCH64_VIRT_ARGS+= -m 1G -smp cpus=4
QEMU_AARCH64_VIRT_ARGS+= -netdev user,id=net0,hostfwd=udp::4445-:2000
QEMU_AARCH64_VIRT_ARGS+= -device e1000e,netdev=net0,mac=12:34:56:11:22:33
QEMU_AARCH64_VIRT_ARGS+= -object filter-dump,id=net0,netdev=net0,file=packets.pcap -nographic

qemu-aarch64-virt:
	qemu-system-aarch64 $(QEMU_AARCH64_VIRT_ARGS)

debug-aarch64-virt:
	qemu-system-aarch64 $(QEMU_AARCH64_VIRT_ARGS) -s -S

gdb-aarch64-virt:
	gdb-multiarch -x scripts/aarch64-debug.gdb

# x86_64

x86_64: x86_64_uefi.img

check_x86_64: $(X86ASM)
	cargo +$(RUSTV) check_x86

kernel-x86_64.elf: $(X86ASM) FORCE
	cargo +$(RUSTV) x86 $(OPT)

x86_64_boot.img: kernel-x86_64.elf
	cargo +$(RUSTV) run --release --package x86bootdisk -- --kernel $< --output $@

x86_64_uefi.img: kernel-x86_64.elf
	cargo +$(RUSTV) run --release --package x86bootdisk -- --kernel $< --output $@ --pxe x86_64_uefi_pxe_boot --boot-type uefi

$(X86ASM): FORCE
	$(MAKE) -C $@


QEMU_X86_ARGS= -drive format=raw,file=x86_64_uefi.img # -d int --trace "e1000e_irq_*" --trace "pci_cfg_*"
QEMU_X86_ARGS+= -machine q35
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
QEMU_X86_NET_ARGS+= -object filter-dump,id=net0,netdev=net0,file=packets.pcap

tcp-dump:
	tcpdump -vvv -XXnr packets.pcap

server:
	python3 scripts/udp.py

qemu-x86_64-net:
	cat /dev/null > packets.pcap
	qemu-system-x86_64  $(QEMU_X86_NET_ARGS) -bios `cat ${HOME}/.ovfmpath`

qemu-x86_64:
	qemu-system-x86_64 $(QEMU_X86_ARGS) -bios `cat ${HOME}/.ovfmpath`

debug-x86_64:
	qemu-system-x86_64 $(QEMU_X86_ARGS) -s -S  -bios `cat ${HOME}/.ovfmpath`

gdb-x86_64:
	gdb-multiarch -x scripts/x86-debug.gdb

# riscv32

riscv32:
	cargo +$(RUSTV) rv32 $(OPT)

check_riscv32: $(X86ASM)
	cargo +$(RUSTV) check_rv32

qemu-riscv32: target/riscv32imac-unknown-none-elf/$(BUILD)/awkernel
	qemu-system-riscv32 -machine virt -bios none -kernel $< -m 1G -nographic -smp 4 -monitor telnet::5556,server,nowait

# Linux / macOS

std: FORCE
	cargo +$(RUSTV) std $(OPT)

check_std: FORCE
	cargo +$(RUSTV) check_std

run-std:
	cargo +$(RUSTV) run --package awkernel --no-default-features --features std $(OPT)

# Docs
docs: FORCE
	mdbook build -d ../docs ./mdbook

# Test

test: FORCE
	cargo test_awkernel_lib
	cargo test_awkernel_async_lib -- --nocapture
	cargo test_awkernel_drivers

loom: FORCE
	RUST_BACKTRACE=1 RUSTFLAGS="--cfg loom" cargo +$(RUSTV) test_awkernel_lib --test model_check_mcslock --release -- --nocapture
	RUST_BACKTRACE=1 RUSTFLAGS="--cfg loom" cargo +$(RUSTV) test_awkernel_lib --test model_check_rwlock --release -- --nocapture

# Format

fmt: FORCE
	cargo +$(RUSTV) fmt

# Clean

clean: FORCE
	rm -rf *.o *.elf $(AARCH64_BSP_LD) *.img kernel/asm/x86/*.o x86_64_uefi_pxe_boot
	cargo clean
	$(MAKE) -C $(X86ASM) clean


## QEMU Monitor

monitor : FORCE
	telnet localhost $(QEMUPORT)

