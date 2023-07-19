ifndef $(BSP)
	BSP = raspi3
endif

ifeq ($(RELEASE), 1)
	OPT = --release
	BUILD = release
else
	BUILD = debug
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


all: aarch64 x86_64 riscv32 std

cargo: target/aarch64-kernel/$(BUILD)/awkernel kernel-x86_64.elf std

FORCE:

# AArch64
aarch64: kernel8.img

target/aarch64-kernel/$(BUILD)/awkernel: $(ASM_OBJ_AARCH64) aarch64-link-bsp.lds FORCE
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +nightly aarch64 $(AARCH64_OPT)

kernel8.img: target/aarch64-kernel/$(BUILD)/awkernel
	rust-objcopy -O binary target/aarch64-kernel/$(BUILD)/awkernel $@

$(ASM_OBJ_AARCH64): $(ASM_FILE_AARCH64) $(ASM_FILE_DEP_AARCH64)
	$(CC) --target=aarch64-elf -c $< -o $@ -DSTACKSIZE="$(STACKSIZE)"

aarch64-link-bsp.lds: aarch64-link.lds
	sed "s/#INITADDR#/$(INITADDR)/" aarch64-link.lds > $@

QEMU_AARCH64_ARGS= -m 1024 -kernel kernel8.img
QEMU_AARCH64_ARGS+= -serial stdio -display none
QEMU_AARCH64_ARGS+=-monitor telnet::$(QEMUPORT),server,nowait # -d int

## Raspi3

QEMU_RASPI3_ARGS= -M raspi3b -dtb bcm2710-rpi-3-b-plus.dtb $(QEMU_AARCH64_ARGS)

qemu-raspi3:
	qemu-system-aarch64 $(QEMU_RASPI3_ARGS)

debug-raspi3:
	qemu-system-aarch64 $(QEMU_RASPI3_ARGS) -s -S

gdb-raspi3:
	gdb-multiarch -x aarch64-debug.gdb

## Virt

QEMU_AARCH64_VIRT_ARGS= -M virt,gic-version=2 -cpu cortex-a72 -smp 8 $(QEMU_AARCH64_ARGS)

qemu-aarch64-virt:
	qemu-system-aarch64 $(QEMU_AARCH64_VIRT_ARGS)

# x86_64

x86_64: x86_64_uefi.img

kernel-x86_64.elf: $(X86ASM) FORCE
	cargo +nightly x86 $(OPT)

x86_64_boot.img: kernel-x86_64.elf
	cargo +nightly run --release --package x86bootdisk -- --kernel $< --output $@

x86_64_uefi.img: kernel-x86_64.elf
	cargo +nightly run --release --package x86bootdisk -- --kernel $< --output $@ --boot-type uefi

$(X86ASM): FORCE
	$(MAKE) -C $@

QEMU_X86_ARGS= -m 512 -drive format=raw,file=x86_64_uefi.img
QEMU_X86_ARGS+= -machine q35
QEMU_X86_ARGS+= -serial stdio -smp 4 -monitor telnet::$(QEMUPORT),server,nowait

qemu-x86_64:
	qemu-system-x86_64 $(QEMU_X86_ARGS) -bios `cat ${HOME}/.ovfmpath`

debug-x86_64:
	qemu-system-x86_64 $(QEMU_X86_ARGS) -s -S  -bios `cat ${HOME}/.ovfmpath`

gdb-x86_64:
	gdb-multiarch -x x86-debug.gdb

# riscv32

riscv32:
	cargo +nightly rv32 $(OPT)

qemu-riscv32: target/riscv32imac-unknown-none-elf/$(BUILD)/awkernel
	qemu-system-riscv32 -machine virt -bios none -kernel $< -m 1G -nographic -smp 4 -monitor telnet::5556,server,nowait

# Linux / macOS

std: FORCE
	cargo +nightly std $(OPT)

run-std:
	cargo +nightly run --package awkernel --no-default-features --features std $(OPT)

# Test

test: FORCE
	cargo test_awkernel_lib
	cargo test_awkernel_async_lib -- --nocapture
	cargo test_awkernel_drivers

# Clean

clean: FORCE
	rm -f *.o *.elf aarch64-link-bsp.lds *.img kernel/asm/x86/*.o
	cargo clean
	$(MAKE) -C $(X86ASM) clean


## QEMU Monitor

monitor : FORCE
	telnet localhost $(QEMUPORT)

