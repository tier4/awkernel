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

QEMU_AARCH64_ARGS= -kernel kernel8.img
QEMU_AARCH64_ARGS+= -serial stdio 
QEMU_AARCH64_ARGS+= -monitor telnet::$(QEMUPORT),server,nowait # -d int

## Raspi3

QEMU_RASPI3_ARGS= -m 1024 -M raspi3b -dtb bcm2710-rpi-3-b-plus.dtb $(QEMU_AARCH64_ARGS)

qemu-raspi3:
	qemu-system-aarch64 $(QEMU_RASPI3_ARGS)

debug-raspi3:
	qemu-system-aarch64 $(QEMU_RASPI3_ARGS) -s -S

gdb-raspi3:
	gdb-multiarch -x scripts/aarch64-debug.gdb

## Virt

QEMU_AARCH64_VIRT_ARGS= -m 8192 -M virt,gic-version=3 -cpu cortex-a72 $(QEMU_AARCH64_ARGS)
QEMU_AARCH64_VIRT_ARGS+= -m 4G -smp cpus=16
QEMU_AARCH64_VIRT_ARGS+= -object memory-backend-ram,size=1G,id=m0
QEMU_AARCH64_VIRT_ARGS+= -object memory-backend-ram,size=1G,id=m1
QEMU_AARCH64_VIRT_ARGS+= -object memory-backend-ram,size=1G,id=m2
QEMU_AARCH64_VIRT_ARGS+= -object memory-backend-ram,size=1G,id=m3
QEMU_AARCH64_VIRT_ARGS+= -numa node,memdev=m0,cpus=0-3,nodeid=0
QEMU_AARCH64_VIRT_ARGS+= -numa node,memdev=m1,cpus=4-7,nodeid=1
QEMU_AARCH64_VIRT_ARGS+= -numa node,memdev=m2,cpus=8-11,nodeid=2
QEMU_AARCH64_VIRT_ARGS+= -numa node,memdev=m3,cpus=12-15,nodeid=3

qemu-aarch64-virt:
	qemu-system-aarch64 $(QEMU_AARCH64_VIRT_ARGS)

debug-aarch64-virt:
	qemu-system-aarch64 $(QEMU_AARCH64_VIRT_ARGS) -s -S

gdb-aarch64-virt:
	gdb-multiarch -x scripts/aarch64-debug.gdb

# x86_64

x86_64: x86_64_uefi.img

kernel-x86_64.elf: $(X86ASM) FORCE
	cargo +nightly x86 $(OPT)

x86_64_boot.img: kernel-x86_64.elf
	cargo +nightly run --release --package x86bootdisk -- --kernel $< --output $@

x86_64_uefi.img: kernel-x86_64.elf
	cargo +nightly run --release --package x86bootdisk -- --kernel $< --output $@ --pxe x86_64_uefi_pxe_boot --boot-type uefi

$(X86ASM): FORCE
	$(MAKE) -C $@


QEMU_X86_ARGS= -m 512 -drive format=raw,file=x86_64_uefi.img
QEMU_X86_ARGS+= -machine q35
QEMU_X86_ARGS+= -serial stdio -smp 4 -monitor telnet::5556,server,nowait

QEMU_X86_NET_ARGS=$(QEMU_X86_ARGS)
QEMU_X86_NET_ARGS+= -netdev user,id=net0,hostfwd=udp::4445-:2000
QEMU_X86_NET_ARGS+= -device e1000e,netdev=net0,mac=12:34:56:11:22:33
QEMU_X86_NET_ARGS+= -object filter-dump,id=net0,netdev=net0,file=packets.pcap

tcp-dump:
	tcpdump -XXnr packets.pcap

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
	rm -rf *.o *.elf aarch64-link-bsp.lds *.img kernel/asm/x86/*.o x86_64_uefi_pxe_boot
	cargo clean
	$(MAKE) -C $(X86ASM) clean


## QEMU Monitor

monitor : FORCE
	telnet localhost $(QEMUPORT)

