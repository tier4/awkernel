use awkernel_lib::delay::wait_forever;
use x86_64::structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode};

static mut IDT: InterruptDescriptorTable = InterruptDescriptorTable::new();

pub unsafe fn init() {
    let ptr = &raw mut IDT;
    let idt = &mut *ptr;

    idt.alignment_check.set_handler_fn(alignment_check);
    idt.bound_range_exceeded
        .set_handler_fn(bound_range_exceeded);
    idt.breakpoint.set_handler_fn(breakpoint);
    idt.debug.set_handler_fn(debug);
    idt.device_not_available
        .set_handler_fn(device_not_available);
    idt.divide_error.set_handler_fn(divide_error);
    idt.double_fault.set_handler_fn(double_fault);
    idt.general_protection_fault
        .set_handler_fn(general_protection_fault);
    idt.invalid_opcode.set_handler_fn(invalid_opcode);
    idt.invalid_tss.set_handler_fn(invalid_tss);
    idt.machine_check.set_handler_fn(machine_check);
    idt.non_maskable_interrupt
        .set_handler_fn(non_maskable_interrupt);
    idt.overflow.set_handler_fn(overflow);
    idt.page_fault.set_handler_fn(page_fault);
    idt.security_exception.set_handler_fn(security_exception);
    idt.segment_not_present.set_handler_fn(segment_not_present);
    idt.simd_floating_point.set_handler_fn(simd_floating_point);
    idt.stack_segment_fault.set_handler_fn(stack_segment_fault);
    idt.virtualization.set_handler_fn(virtualization);
    idt.vmm_communication_exception
        .set_handler_fn(vmm_communication_exception);
    idt.x87_floating_point.set_handler_fn(x87_floating_point);

    idt[0].set_handler_fn(irq11);

    idt[32].set_handler_fn(irq32);
    idt[33].set_handler_fn(irq33);
    idt[34].set_handler_fn(irq34);
    idt[35].set_handler_fn(irq35);
    idt[36].set_handler_fn(irq36);
    idt[37].set_handler_fn(irq37);
    idt[38].set_handler_fn(irq38);
    idt[39].set_handler_fn(irq39);
    idt[40].set_handler_fn(irq40);
    idt[41].set_handler_fn(irq41);
    idt[42].set_handler_fn(irq42);
    idt[43].set_handler_fn(irq43);
    idt[44].set_handler_fn(irq44);
    idt[45].set_handler_fn(irq45);
    idt[46].set_handler_fn(irq46);
    idt[47].set_handler_fn(irq47);
    idt[48].set_handler_fn(irq48);
    idt[49].set_handler_fn(irq49);
    idt[50].set_handler_fn(irq50);
    idt[51].set_handler_fn(irq51);
    idt[52].set_handler_fn(irq52);
    idt[53].set_handler_fn(irq53);
    idt[54].set_handler_fn(irq54);
    idt[55].set_handler_fn(irq55);
    idt[56].set_handler_fn(irq56);
    idt[57].set_handler_fn(irq57);
    idt[58].set_handler_fn(irq58);
    idt[59].set_handler_fn(irq59);
    idt[60].set_handler_fn(irq60);
    idt[61].set_handler_fn(irq61);
    idt[62].set_handler_fn(irq62);
    idt[63].set_handler_fn(irq63);
    idt[64].set_handler_fn(irq64);
    idt[65].set_handler_fn(irq65);
    idt[66].set_handler_fn(irq66);
    idt[67].set_handler_fn(irq67);
    idt[68].set_handler_fn(irq68);
    idt[69].set_handler_fn(irq69);
    idt[70].set_handler_fn(irq70);
    idt[71].set_handler_fn(irq71);
    idt[72].set_handler_fn(irq72);
    idt[73].set_handler_fn(irq73);
    idt[74].set_handler_fn(irq74);
    idt[75].set_handler_fn(irq75);
    idt[76].set_handler_fn(irq76);
    idt[77].set_handler_fn(irq77);
    idt[78].set_handler_fn(irq78);
    idt[79].set_handler_fn(irq79);
    idt[80].set_handler_fn(irq80);
    idt[81].set_handler_fn(irq81);
    idt[82].set_handler_fn(irq82);
    idt[83].set_handler_fn(irq83);
    idt[84].set_handler_fn(irq84);
    idt[85].set_handler_fn(irq85);
    idt[86].set_handler_fn(irq86);
    idt[87].set_handler_fn(irq87);
    idt[88].set_handler_fn(irq88);
    idt[89].set_handler_fn(irq89);
    idt[90].set_handler_fn(irq90);
    idt[91].set_handler_fn(irq91);
    idt[92].set_handler_fn(irq92);
    idt[93].set_handler_fn(irq93);
    idt[94].set_handler_fn(irq94);
    idt[95].set_handler_fn(irq95);
    idt[96].set_handler_fn(irq96);
    idt[97].set_handler_fn(irq97);
    idt[98].set_handler_fn(irq98);
    idt[99].set_handler_fn(irq99);
    idt[100].set_handler_fn(irq100);
    idt[101].set_handler_fn(irq101);
    idt[102].set_handler_fn(irq102);
    idt[103].set_handler_fn(irq103);
    idt[104].set_handler_fn(irq104);
    idt[105].set_handler_fn(irq105);
    idt[106].set_handler_fn(irq106);
    idt[107].set_handler_fn(irq107);
    idt[108].set_handler_fn(irq108);
    idt[109].set_handler_fn(irq109);
    idt[110].set_handler_fn(irq110);
    idt[111].set_handler_fn(irq111);
    idt[112].set_handler_fn(irq112);
    idt[113].set_handler_fn(irq113);
    idt[114].set_handler_fn(irq114);
    idt[115].set_handler_fn(irq115);
    idt[116].set_handler_fn(irq116);
    idt[117].set_handler_fn(irq117);
    idt[118].set_handler_fn(irq118);
    idt[119].set_handler_fn(irq119);
    idt[120].set_handler_fn(irq120);
    idt[121].set_handler_fn(irq121);
    idt[122].set_handler_fn(irq122);
    idt[123].set_handler_fn(irq123);
    idt[124].set_handler_fn(irq124);
    idt[125].set_handler_fn(irq125);
    idt[126].set_handler_fn(irq126);
    idt[127].set_handler_fn(irq127);
    idt[128].set_handler_fn(irq128);
    idt[129].set_handler_fn(irq129);
    idt[130].set_handler_fn(irq130);
    idt[131].set_handler_fn(irq131);
    idt[132].set_handler_fn(irq132);
    idt[133].set_handler_fn(irq133);
    idt[134].set_handler_fn(irq134);
    idt[135].set_handler_fn(irq135);
    idt[136].set_handler_fn(irq136);
    idt[137].set_handler_fn(irq137);
    idt[138].set_handler_fn(irq138);
    idt[139].set_handler_fn(irq139);
    idt[140].set_handler_fn(irq140);
    idt[141].set_handler_fn(irq141);
    idt[142].set_handler_fn(irq142);
    idt[143].set_handler_fn(irq143);
    idt[144].set_handler_fn(irq144);
    idt[145].set_handler_fn(irq145);
    idt[146].set_handler_fn(irq146);
    idt[147].set_handler_fn(irq147);
    idt[148].set_handler_fn(irq148);
    idt[149].set_handler_fn(irq149);
    idt[150].set_handler_fn(irq150);
    idt[151].set_handler_fn(irq151);
    idt[152].set_handler_fn(irq152);
    idt[153].set_handler_fn(irq153);
    idt[154].set_handler_fn(irq154);
    idt[155].set_handler_fn(irq155);
    idt[156].set_handler_fn(irq156);
    idt[157].set_handler_fn(irq157);
    idt[158].set_handler_fn(irq158);
    idt[159].set_handler_fn(irq159);
    idt[160].set_handler_fn(irq160);
    idt[161].set_handler_fn(irq161);
    idt[162].set_handler_fn(irq162);
    idt[163].set_handler_fn(irq163);
    idt[164].set_handler_fn(irq164);
    idt[165].set_handler_fn(irq165);
    idt[166].set_handler_fn(irq166);
    idt[167].set_handler_fn(irq167);
    idt[168].set_handler_fn(irq168);
    idt[169].set_handler_fn(irq169);
    idt[170].set_handler_fn(irq170);
    idt[171].set_handler_fn(irq171);
    idt[172].set_handler_fn(irq172);
    idt[173].set_handler_fn(irq173);
    idt[174].set_handler_fn(irq174);
    idt[175].set_handler_fn(irq175);
    idt[176].set_handler_fn(irq176);
    idt[177].set_handler_fn(irq177);
    idt[178].set_handler_fn(irq178);
    idt[179].set_handler_fn(irq179);
    idt[180].set_handler_fn(irq180);
    idt[181].set_handler_fn(irq181);
    idt[182].set_handler_fn(irq182);
    idt[183].set_handler_fn(irq183);
    idt[184].set_handler_fn(irq184);
    idt[185].set_handler_fn(irq185);
    idt[186].set_handler_fn(irq186);
    idt[187].set_handler_fn(irq187);
    idt[188].set_handler_fn(irq188);
    idt[189].set_handler_fn(irq189);
    idt[190].set_handler_fn(irq190);
    idt[191].set_handler_fn(irq191);
    idt[192].set_handler_fn(irq192);
    idt[193].set_handler_fn(irq193);
    idt[194].set_handler_fn(irq194);
    idt[195].set_handler_fn(irq195);
    idt[196].set_handler_fn(irq196);
    idt[197].set_handler_fn(irq197);
    idt[198].set_handler_fn(irq198);
    idt[199].set_handler_fn(irq199);
    idt[200].set_handler_fn(irq200);
    idt[201].set_handler_fn(irq201);
    idt[202].set_handler_fn(irq202);
    idt[203].set_handler_fn(irq203);
    idt[204].set_handler_fn(irq204);
    idt[205].set_handler_fn(irq205);
    idt[206].set_handler_fn(irq206);
    idt[207].set_handler_fn(irq207);
    idt[208].set_handler_fn(irq208);
    idt[209].set_handler_fn(irq209);
    idt[210].set_handler_fn(irq210);
    idt[211].set_handler_fn(irq211);
    idt[212].set_handler_fn(irq212);
    idt[213].set_handler_fn(irq213);
    idt[214].set_handler_fn(irq214);
    idt[215].set_handler_fn(irq215);
    idt[216].set_handler_fn(irq216);
    idt[217].set_handler_fn(irq217);
    idt[218].set_handler_fn(irq218);
    idt[219].set_handler_fn(irq219);
    idt[220].set_handler_fn(irq220);
    idt[221].set_handler_fn(irq221);
    idt[222].set_handler_fn(irq222);
    idt[223].set_handler_fn(irq223);
    idt[224].set_handler_fn(irq224);
    idt[225].set_handler_fn(irq225);
    idt[226].set_handler_fn(irq226);
    idt[227].set_handler_fn(irq227);
    idt[228].set_handler_fn(irq228);
    idt[229].set_handler_fn(irq229);
    idt[230].set_handler_fn(irq230);
    idt[231].set_handler_fn(irq231);
    idt[232].set_handler_fn(irq232);
    idt[233].set_handler_fn(irq233);
    idt[234].set_handler_fn(irq234);
    idt[235].set_handler_fn(irq235);
    idt[236].set_handler_fn(irq236);
    idt[237].set_handler_fn(irq237);
    idt[238].set_handler_fn(irq238);
    idt[239].set_handler_fn(irq239);
    idt[240].set_handler_fn(irq240);
    idt[241].set_handler_fn(irq241);
    idt[242].set_handler_fn(irq242);
    idt[243].set_handler_fn(irq243);
    idt[244].set_handler_fn(irq244);
    idt[245].set_handler_fn(irq245);
    idt[246].set_handler_fn(irq246);
    idt[247].set_handler_fn(irq247);
    idt[248].set_handler_fn(irq248);
    idt[249].set_handler_fn(irq249);
    idt[250].set_handler_fn(irq250);
    idt[251].set_handler_fn(irq251);
    idt[252].set_handler_fn(irq252);
    idt[253].set_handler_fn(irq253);
    idt[254].set_handler_fn(irq254);

    idt[255].set_handler_fn(preemption);

    idt.load();
}

pub unsafe fn load() {
    let ptr = &raw mut IDT;
    let idt = &mut *ptr;
    idt.load();
}

extern "x86-interrupt" fn irq11(_stack_frame: InterruptStackFrame) {
    log::debug!("IRQ11");
}

macro_rules! irq_handler {
    ($name:ident, $id:expr) => {
        extern "x86-interrupt" fn $name(_stack_frame: InterruptStackFrame) {
            awkernel_lib::interrupt::eoi(); // End of interrupt.
            awkernel_lib::interrupt::handle_irq($id);
        }
    };
}

irq_handler!(irq32, 32);
irq_handler!(irq33, 33);
irq_handler!(irq34, 34);
irq_handler!(irq35, 35);
irq_handler!(irq36, 36);
irq_handler!(irq37, 37);
irq_handler!(irq38, 38);
irq_handler!(irq39, 39);
irq_handler!(irq40, 40);
irq_handler!(irq41, 41);
irq_handler!(irq42, 42);
irq_handler!(irq43, 43);
irq_handler!(irq44, 44);
irq_handler!(irq45, 45);
irq_handler!(irq46, 46);
irq_handler!(irq47, 47);
irq_handler!(irq48, 48);
irq_handler!(irq49, 49);
irq_handler!(irq50, 50);
irq_handler!(irq51, 51);
irq_handler!(irq52, 52);
irq_handler!(irq53, 53);
irq_handler!(irq54, 54);
irq_handler!(irq55, 55);
irq_handler!(irq56, 56);
irq_handler!(irq57, 57);
irq_handler!(irq58, 58);
irq_handler!(irq59, 59);
irq_handler!(irq60, 60);
irq_handler!(irq61, 61);
irq_handler!(irq62, 62);
irq_handler!(irq63, 63);
irq_handler!(irq64, 64);
irq_handler!(irq65, 65);
irq_handler!(irq66, 66);
irq_handler!(irq67, 67);
irq_handler!(irq68, 68);
irq_handler!(irq69, 69);
irq_handler!(irq70, 70);
irq_handler!(irq71, 71);
irq_handler!(irq72, 72);
irq_handler!(irq73, 73);
irq_handler!(irq74, 74);
irq_handler!(irq75, 75);
irq_handler!(irq76, 76);
irq_handler!(irq77, 77);
irq_handler!(irq78, 78);
irq_handler!(irq79, 79);
irq_handler!(irq80, 80);
irq_handler!(irq81, 81);
irq_handler!(irq82, 82);
irq_handler!(irq83, 83);
irq_handler!(irq84, 84);
irq_handler!(irq85, 85);
irq_handler!(irq86, 86);
irq_handler!(irq87, 87);
irq_handler!(irq88, 88);
irq_handler!(irq89, 89);
irq_handler!(irq90, 90);
irq_handler!(irq91, 91);
irq_handler!(irq92, 92);
irq_handler!(irq93, 93);
irq_handler!(irq94, 94);
irq_handler!(irq95, 95);
irq_handler!(irq96, 96);
irq_handler!(irq97, 97);
irq_handler!(irq98, 98);
irq_handler!(irq99, 99);
irq_handler!(irq100, 100);
irq_handler!(irq101, 101);
irq_handler!(irq102, 102);
irq_handler!(irq103, 103);
irq_handler!(irq104, 104);
irq_handler!(irq105, 105);
irq_handler!(irq106, 106);
irq_handler!(irq107, 107);
irq_handler!(irq108, 108);
irq_handler!(irq109, 109);
irq_handler!(irq110, 110);
irq_handler!(irq111, 111);
irq_handler!(irq112, 112);
irq_handler!(irq113, 113);
irq_handler!(irq114, 114);
irq_handler!(irq115, 115);
irq_handler!(irq116, 116);
irq_handler!(irq117, 117);
irq_handler!(irq118, 118);
irq_handler!(irq119, 119);
irq_handler!(irq120, 120);
irq_handler!(irq121, 121);
irq_handler!(irq122, 122);
irq_handler!(irq123, 123);
irq_handler!(irq124, 124);
irq_handler!(irq125, 125);
irq_handler!(irq126, 126);
irq_handler!(irq127, 127);
irq_handler!(irq128, 128);
irq_handler!(irq129, 129);
irq_handler!(irq130, 130);
irq_handler!(irq131, 131);
irq_handler!(irq132, 132);
irq_handler!(irq133, 133);
irq_handler!(irq134, 134);
irq_handler!(irq135, 135);
irq_handler!(irq136, 136);
irq_handler!(irq137, 137);
irq_handler!(irq138, 138);
irq_handler!(irq139, 139);
irq_handler!(irq140, 140);
irq_handler!(irq141, 141);
irq_handler!(irq142, 142);
irq_handler!(irq143, 143);
irq_handler!(irq144, 144);
irq_handler!(irq145, 145);
irq_handler!(irq146, 146);
irq_handler!(irq147, 147);
irq_handler!(irq148, 148);
irq_handler!(irq149, 149);
irq_handler!(irq150, 150);
irq_handler!(irq151, 151);
irq_handler!(irq152, 152);
irq_handler!(irq153, 153);
irq_handler!(irq154, 154);
irq_handler!(irq155, 155);
irq_handler!(irq156, 156);
irq_handler!(irq157, 157);
irq_handler!(irq158, 158);
irq_handler!(irq159, 159);
irq_handler!(irq160, 160);
irq_handler!(irq161, 161);
irq_handler!(irq162, 162);
irq_handler!(irq163, 163);
irq_handler!(irq164, 164);
irq_handler!(irq165, 165);
irq_handler!(irq166, 166);
irq_handler!(irq167, 167);
irq_handler!(irq168, 168);
irq_handler!(irq169, 169);
irq_handler!(irq170, 170);
irq_handler!(irq171, 171);
irq_handler!(irq172, 172);
irq_handler!(irq173, 173);
irq_handler!(irq174, 174);
irq_handler!(irq175, 175);
irq_handler!(irq176, 176);
irq_handler!(irq177, 177);
irq_handler!(irq178, 178);
irq_handler!(irq179, 179);
irq_handler!(irq180, 180);
irq_handler!(irq181, 181);
irq_handler!(irq182, 182);
irq_handler!(irq183, 183);
irq_handler!(irq184, 184);
irq_handler!(irq185, 185);
irq_handler!(irq186, 186);
irq_handler!(irq187, 187);
irq_handler!(irq188, 188);
irq_handler!(irq189, 189);
irq_handler!(irq190, 190);
irq_handler!(irq191, 191);
irq_handler!(irq192, 192);
irq_handler!(irq193, 193);
irq_handler!(irq194, 194);
irq_handler!(irq195, 195);
irq_handler!(irq196, 196);
irq_handler!(irq197, 197);
irq_handler!(irq198, 198);
irq_handler!(irq199, 199);
irq_handler!(irq200, 200);
irq_handler!(irq201, 201);
irq_handler!(irq202, 202);
irq_handler!(irq203, 203);
irq_handler!(irq204, 204);
irq_handler!(irq205, 205);
irq_handler!(irq206, 206);
irq_handler!(irq207, 207);
irq_handler!(irq208, 208);
irq_handler!(irq209, 209);
irq_handler!(irq210, 210);
irq_handler!(irq211, 211);
irq_handler!(irq212, 212);
irq_handler!(irq213, 213);
irq_handler!(irq214, 214);
irq_handler!(irq215, 215);
irq_handler!(irq216, 216);
irq_handler!(irq217, 217);
irq_handler!(irq218, 218);
irq_handler!(irq219, 219);
irq_handler!(irq220, 220);
irq_handler!(irq221, 221);
irq_handler!(irq222, 222);
irq_handler!(irq223, 223);
irq_handler!(irq224, 224);
irq_handler!(irq225, 225);
irq_handler!(irq226, 226);
irq_handler!(irq227, 227);
irq_handler!(irq228, 228);
irq_handler!(irq229, 229);
irq_handler!(irq230, 230);
irq_handler!(irq231, 231);
irq_handler!(irq232, 232);
irq_handler!(irq233, 233);
irq_handler!(irq234, 234);
irq_handler!(irq235, 235);
irq_handler!(irq236, 236);
irq_handler!(irq237, 237);
irq_handler!(irq238, 238);
irq_handler!(irq239, 239);
irq_handler!(irq240, 240);
irq_handler!(irq241, 241);
irq_handler!(irq242, 242);
irq_handler!(irq243, 243);
irq_handler!(irq244, 244);
irq_handler!(irq245, 245);
irq_handler!(irq246, 246);
irq_handler!(irq247, 247);
irq_handler!(irq248, 248);
irq_handler!(irq249, 249);
irq_handler!(irq250, 250);
irq_handler!(irq251, 251);
irq_handler!(irq252, 252);
irq_handler!(irq253, 253);
irq_handler!(irq254, 254);

extern "x86-interrupt" fn preemption(_stack_frame: InterruptStackFrame) {
    awkernel_lib::interrupt::eoi(); // End of interrupt.
    awkernel_lib::interrupt::handle_preemption();
}

extern "x86-interrupt" fn alignment_check(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "alignment check: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn bound_range_exceeded(stack_frame: InterruptStackFrame) {
    log::debug!("bound range exceeded: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn breakpoint(stack_frame: InterruptStackFrame) {
    log::debug!("breakpoint: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn debug(stack_frame: InterruptStackFrame) {
    log::debug!("debug: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn device_not_available(stack_frame: InterruptStackFrame) {
    log::debug!("device not available: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn divide_error(stack_frame: InterruptStackFrame) {
    log::debug!("divide error: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn double_fault(stack_frame: InterruptStackFrame, error: u64) -> ! {
    log::debug!(
        "double fault: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
    wait_forever()
}

extern "x86-interrupt" fn general_protection_fault(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "general protection fault: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn invalid_opcode(stack_frame: InterruptStackFrame) {
    log::debug!("invalid opcode: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn invalid_tss(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "invalid tss: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn machine_check(stack_frame: InterruptStackFrame) -> ! {
    log::debug!("machine check: stack_frame = {:?}", stack_frame,);
    wait_forever()
}

extern "x86-interrupt" fn non_maskable_interrupt(stack_frame: InterruptStackFrame) {
    log::debug!("non maskable interrupt: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn overflow(stack_frame: InterruptStackFrame) {
    log::debug!("overflow: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn page_fault(stack_frame: InterruptStackFrame, error: PageFaultErrorCode) {
    let addr = x86_64::registers::control::Cr2::read();

    log::debug!(
        "page fault: addr = {:?}, stack_frame = {:?}, error = {:b}",
        addr,
        stack_frame,
        error.bits()
    );
}

extern "x86-interrupt" fn security_exception(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "security exception: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn segment_not_present(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "segment not present: cpu = {}, stack_frame = {:?}, error = {error}",
        awkernel_lib::cpu::cpu_id(),
        stack_frame,
    );
}

extern "x86-interrupt" fn simd_floating_point(stack_frame: InterruptStackFrame) {
    log::debug!("simd floating point: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn stack_segment_fault(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "stack segment fault: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn virtualization(stack_frame: InterruptStackFrame) {
    log::debug!("virtualization: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn vmm_communication_exception(
    stack_frame: InterruptStackFrame,
    error: u64,
) {
    log::debug!(
        "vmm communication exception: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn x87_floating_point(stack_frame: InterruptStackFrame) {
    log::debug!("x87 floating point: stack_frame = {:?}", stack_frame,);
}
