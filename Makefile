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

ASM_FILE_DEP=kernel/asm/device/raspi.S kernel/asm/exception.S
ASM_FILE=kernel/asm/boot.S
ASM_OBJ=boot_aarch64.o

ifndef $(CC)
	CC = clang
endif

ifndef $(LD)
	LD = rust-lld -flavor gnu
endif

all: raspi3 x86_64

raspi3: kernel-aarch64.img

.PHONY: target/aarch64-custom/$(BUILD)/t4os
target/aarch64-custom/$(BUILD)/t4os: $(ASM_OBJ) aarch64-link-bsp.lds
	cargo +nightly raspi3 $(OPT)

kernel-aarch64.img: target/aarch64-custom/$(BUILD)/t4os
	rust-objcopy -O binary target/aarch64-custom/$(BUILD)/t4os $@

x86_64:
	cargo +nightly x86 $(OPT)

$(ASM_OBJ): $(ASM_FILE) $(ASM_FILE_DEP)
	$(CC) --target=aarch64-elf -c $(ASM_FILE) -o $(ASM_OBJ) -D$(BSP) -DSTACKSIZE="$(STACKSIZE)"

aarch64-link-bsp.lds: aarch64-link.lds
	sed "s/#INITADDR#/$(INITADDR)/" aarch64-link.lds | sed "s/#STACKSIZE#/$(STACKSIZE)/" | sed "s/#NUMCPU#/$(NUMCPU)/" > $@

clean:
	rm -f *.o *.elf aarch64-link-bsp.lds *.img
	cargo clean
