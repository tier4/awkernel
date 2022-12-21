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

all: raspi x86_64 linux

cargo: target/aarch64-custom/$(BUILD)/t4os kernel-x86_64.elf linux

FORCE:

# AArch64
raspi: kernel-aarch64.img

target/aarch64-custom/$(BUILD)/t4os: $(ASM_OBJ_AARCH64) aarch64-link-bsp.lds kernel FORCE
	RUSTFLAGS="$(RUSTC_MISC_ARGS)" cargo +nightly $(BSP) $(OPT)

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

kernel-x86_64.elf: $(X86ASM) FORCE
	cargo +nightly x86 $(OPT)

x86_64_boot.img: kernel-x86_64.elf
	cargo run --release --package x86bootdisk -- --kernel $< --output $@

$(X86ASM): FORCE
	$(MAKE) -C $@

qemu-x86_64:
	qemu-system-x86_64 -drive format=raw,file=x86_64_boot.img -serial stdio -smp 4
	# qemu-system-x86_64 -drive format=raw,file=x86_64_boot.img -monitor stdio -smp 4 -d int

## Linux

linux: FORCE
	cargo +nightly linux $(OPT)

run-linux:
	cargo +nightly run --package t4os --no-default-features --features linux $(OPT)

## Clean

clean: FORCE
	rm -f *.o *.elf aarch64-link-bsp.lds *.img kernel/asm/x86/*.o
	cargo clean --package t4os
	$(MAKE) -C $(X86ASM) clean
