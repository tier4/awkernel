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

# 4 CPUs
NUMCPU = 4

ifeq ($(BSP),raspi3)
	RUSTC_MISC_ARGS = -C target-cpu=cortex-a53
	INITADDR = 0x80000
else ifeq ($(BSP),raspi4)
	RUSTC_MISC_ARGS = -C target-cpu=cortex-a72
	INITADDR = 0
endif

ASM_FILE_DEP_AARCH64=kernel/asm/aarch64/device/raspi.S kernel/asm/aarch64/exception.S
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

all: raspi x86_64 std

cargo: target/aarch64-kernel/$(BUILD)/awkernel kernel-x86_64.elf std

FORCE:

# AArch64
raspi: kernel8.img

target/aarch64-kernel/$(BUILD)/awkernel: $(ASM_OBJ_AARCH64) aarch64-link-bsp.lds kernel FORCE
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +nightly $(BSP) $(OPT)

kernel8.img: target/aarch64-kernel/$(BUILD)/awkernel
	rust-objcopy -O binary target/aarch64-kernel/$(BUILD)/awkernel $@

$(ASM_OBJ_AARCH64): $(ASM_FILE_AARCH64) $(ASM_FILE_DEP_AARCH64)
	$(CC) --target=aarch64-elf -c $< -o $@ -D$(BSP) -DSTACKSIZE="$(STACKSIZE)"

aarch64-link-bsp.lds: aarch64-link.lds
	sed "s/#INITADDR#/$(INITADDR)/" aarch64-link.lds | sed "s/#STACKSIZE#/$(STACKSIZE)/" | sed "s/#NUMCPU#/$(NUMCPU)/" > $@

qemu-raspi3:
	qemu-system-aarch64 -m 1024 -M raspi3 -kernel kernel8.img -serial stdio -display none -monitor telnet::5556,server,nowait -d int

debug-raspi3:
	qemu-system-aarch64 -m 1024 -M raspi3b -kernel kernel8.img -serial stdio -display none -monitor telnet::5556,server,nowait -d int -s -S

gdb-raspi3:
	gdb-multiarch -x aarch64-debug.gdb

## x86_64

x86_64: x86_64_boot.img

kernel-x86_64.elf: $(X86ASM) FORCE
	cargo +nightly x86 $(OPT)

x86_64_boot.img: kernel-x86_64.elf
	cargo +nightly run --release --package x86bootdisk -- --kernel $< --output $@

x86_64_uefi.img: kernel-x86_64.elf
	cargo +nightly run --release --package x86bootdisk -- --kernel $< --output $@ --boot-type uefi

$(X86ASM): FORCE
	$(MAKE) -C $@

qemu-x86_64:
	qemu-system-x86_64 -m 512 -drive format=raw,file=x86_64_boot.img -serial stdio -smp 4 -monitor telnet::5556,server,nowait

debug-x86_64:
	qemu-system-x86_64 -m 512 -drive format=raw,file=x86_64_boot.img -serial stdio -smp 4 -display none -monitor telnet::5556,server,nowait -s -S

gdb-x86_64:
	gdb-multiarch -x x86-debug.gdb

## riscv32

riscv32:
	cargo rv32

run-riscv32: target/riscv32imac-unknown-none-elf/debug/awkernel
#	qemu-system-riscv32 -machine virt -bios none -kernel $< -m 512M -nographic -smp 2
	~/ladybird/sim/launch_sim $< --ebreak --htif --tohost 0x80040f88 --fromhost 0x80040f90 --core 2

## Linux / macOS

std: FORCE
	cargo +nightly std $(OPT)

run-std:
	cargo +nightly run --package awkernel --no-default-features --features std $(OPT)

## Test

test: FORCE
	cargo test_awkernel_lib
	cargo test_awkernel_async_lib -- --nocapture
	cargo test_awkernel_drivers

## Clean

clean: FORCE
	rm -f *.o *.elf aarch64-link-bsp.lds *.img kernel/asm/x86/*.o
	cargo clean
	$(MAKE) -C $(X86ASM) clean
