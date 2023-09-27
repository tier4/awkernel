ASM_FILE_X86_16=boot16.S
ASM_OBJ_X86_16=boot16.o
ASM_ELF_X86_16=boot16.elf
ASM_IMG_X86_16=boot16.img

ASM_FILE_X86_32=entry32.S
ASM_OBJ_X86_32=entry32.o
ASM_ELF_X86_32=entry32.elf
ASM_IMG_X86_32=entry32.img

all: $(ASM_IMG_X86_32) $(ASM_IMG_X86_16)

$(ASM_OBJ_X86_16): $(ASM_FILE_X86_16)
	$(CC) -m32 -fno-pie -nostdlib -c $< -o $@

# See kernel::arch::x86_64::kernel_main::NON_PRIMARY_START
$(ASM_ELF_X86_16): $(ASM_OBJ_X86_16)
	$(LD) -m elf_i386 -N -e _start_cpu -Ttext 0xE000 $< -o $@

$(ASM_OBJ_X86_32): $(ASM_FILE_X86_32)
	$(CC) -fno-pie -nostdlib -c $< -o $@

# See kernel::arch::x86_64::kernel_main::ENTRY32
$(ASM_ELF_X86_32): $(ASM_OBJ_X86_32)
	$(LD) -N -e _entry32 -Ttext 0xE400 $< -o $@

%.img: %.elf
	rust-objcopy -O binary $< $@

clean:
	rm -f *.o *.img *.elf
