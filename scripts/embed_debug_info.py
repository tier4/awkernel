import argparse
from elftools.elf.elffile import ELFFile

def main():
    parser = argparse.ArgumentParser(description="Copy the data of each debug section to the rodata-segment")
    parser.add_argument("kernel", help="Kernel ELF file")
    args = parser.parse_args()

    with open(args.kernel, "r+b") as f:
        elf = ELFFile(f)

        # Find the segment that contains ".debug" section assuming it is defined in the linker script
        debug_section = elf.get_section_by_name(".debug")
        assert debug_section is not None
        target_segment = next((segment for segment in elf.iter_segments() if segment.section_in_segment(debug_section)), None)
        if target_segment is None: return

        # Copy the data of each debug section to the target segment
        debug_sections = {section.name : section for section in elf.iter_sections() if section.name.startswith(".debug")}
        symtab = elf.get_section_by_name(".symtab")
        
        f.seek(0)
        image = bytearray(f.read())

        for name, section in debug_sections.items():
            start_sym = symtab.get_symbol_by_name(f'__{name[1:]}_start')
            size_sym = symtab.get_symbol_by_name(f'__{name[1:]}_size')

            if start_sym is None or size_sym is None:
                continue
            
            addr_start_sym = start_sym[0]['st_value']
            addr_size_sym = size_sym[0]['st_value']

            offset = target_segment['p_offset'] + (addr_start_sym - target_segment['p_vaddr'])
            data = section.data()
            assert len(data) == addr_size_sym
            image[offset:offset+len(data)] = data
        
        f.seek(0)
        f.write(image)

if __name__ == '__main__':
    main()