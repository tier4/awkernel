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

ASM_FILE_X86=kernel/asm/x86/boot.S
ASM_OBJ_X86=boot_x86.o

ifndef $(CC)
	CC = clang
endif

ifndef $(LD)
	LD = rust-lld -flavor gnu
endif

all: raspi3 x86_64 linux

raspi3: kernel-aarch64.img

# AArch64
.PHONY: target/aarch64-custom/$(BUILD)/t4os
target/aarch64-custom/$(BUILD)/t4os: $(ASM_OBJ_AARCH64) aarch64-link-bsp.lds
	cargo +nightly raspi3 $(OPT)

kernel-aarch64.img: target/aarch64-custom/$(BUILD)/t4os
	rust-objcopy -O binary target/aarch64-custom/$(BUILD)/t4os $@

$(ASM_OBJ_AARCH64): $(ASM_FILE_AARCH64) $(ASM_FILE_DEP_AARCH64)
	$(CC) --target=aarch64-elf -c $(ASM_FILE_AARCH64) -o $@ -D$(BSP) -DSTACKSIZE="$(STACKSIZE)"

aarch64-link-bsp.lds: aarch64-link.lds
	sed "s/#INITADDR#/$(INITADDR)/" aarch64-link.lds | sed "s/#STACKSIZE#/$(STACKSIZE)/" | sed "s/#NUMCPU#/$(NUMCPU)/" > $@

run-raspi3:
	qemu-system-aarch64 -M raspi3b -kernel kernel-aarch64.img -serial stdio

## x86_64

.PHONY:
x86_64: $(ASM_OBJ_X86)
	cargo +nightly x86 $(OPT)

$(ASM_OBJ_X86): $(ASM_FILE_X86)
	$(CC) -c $(ASM_FILE_X86) -o $@ -DSTACKSIZE="$(STACKSIZE)"

## Linux

.PHONY:
linux:
	cargo +nightly linux $(OPT)

run-linux:
	cargo +nightly run --package t4os --no-default-features --features linux  $(OPT)

## Clean

clean:
	rm -f *.o *.elf aarch64-link-bsp.lds *.img
	cargo clean
