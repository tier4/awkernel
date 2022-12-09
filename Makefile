# Default to the Pine64
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

ASM_FILE_X86_16=kernel/asm/x86/boot16.S
ASM_OBJ_X86_16=kernel/asm/x86/boot16.o
ASM_ELF_X86_16=kernel/asm/x86/boot16.elf
ASM_IMG_X86_16=kernel/asm/x86/boot16.img

ifndef $(CC)
	CC = clang
endif

ifndef $(LD)
	LD = rust-lld -flavor gnu
	# LD = ld.gold
endif

all: raspi3 x86_64 linux

cargo: target/aarch64-custom/$(BUILD)/t4os kernel-x86_64.elf linux

# AArch64
raspi3: target/aarch64-custom/$(BUILD)/t4os

.PHONY: target/aarch64-custom/$(BUILD)/t4os
target/aarch64-custom/$(BUILD)/t4os: $(ASM_OBJ_AARCH64) aarch64-link-bsp.lds kernel
	cargo +nightly raspi3 $(OPT)

kernel-aarch64.img: target/aarch64-custom/$(BUILD)/t4os
	rust-objcopy -O binary target/aarch64-custom/$(BUILD)/t4os $@

$(ASM_OBJ_AARCH64): $(ASM_FILE_AARCH64) $(ASM_FILE_DEP_AARCH64)
	$(CC) --target=aarch64-elf -c $< -o $@ -D$(BSP) -DSTACKSIZE="$(STACKSIZE)"

aarch64-link-bsp.lds: aarch64-link.lds
	sed "s/#INITADDR#/$(INITADDR)/" aarch64-link.lds | sed "s/#STACKSIZE#/$(STACKSIZE)/" | sed "s/#NUMCPU#/$(NUMCPU)/" > $@

qemu-raspi3:
	qemu-system-aarch64 -M raspi3b -kernel kernel-aarch64.img -serial stdio

## x86_64

x86_64: x86_64_boot.img

.PHONY: kernel-x86_64.elf
kernel-x86_64.elf: $(ASM_IMG_X86_16)
	cargo +nightly x86 $(OPT)

x86_64_boot.img: kernel-x86_64.elf
	cargo run --release --package x86bootdisk -- --kernel $< --output $@

$(ASM_OBJ_X86_16): $(ASM_FILE_X86_16)
	$(CC) -m32 -fno-pie -nostdlib -c $< -o $(ASM_OBJ_X86_16)

$(ASM_ELF_X86_16): $(ASM_OBJ_X86_16)
	$(LD) -m elf_i386 -N -e _start_cpu -Ttext 0x1000 $< -o $@

$(ASM_IMG_X86_16): $(ASM_ELF_X86_16)
	rust-objcopy -O binary $< $@

qemu-x86_64:
	qemu-system-x86_64 -drive format=raw,file=x86_64_boot.img -serial stdio -smp 2

## Linux

.PHONY: linux
linux:
	cargo +nightly linux $(OPT)

run-linux:
	cargo +nightly run --package t4os --no-default-features --features linux $(OPT)

## Clean

clean:
	rm -f *.o *.elf aarch64-link-bsp.lds *.img kernel/asm/x86/*.o
	cargo clean
