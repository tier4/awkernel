use awkernel_lib::delay::wait_forever;
use x86_64::structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode};

static mut IDT: InterruptDescriptorTable = InterruptDescriptorTable::new();

pub unsafe fn init() {
    IDT.alignment_check.set_handler_fn(alignment_check);
    IDT.bound_range_exceeded
        .set_handler_fn(bound_range_exceeded);
    IDT.breakpoint.set_handler_fn(breakpoint);
    IDT.debug.set_handler_fn(debug);
    IDT.device_not_available
        .set_handler_fn(device_not_available);
    IDT.divide_error.set_handler_fn(divide_error);
    IDT.double_fault.set_handler_fn(double_fault);
    IDT.general_protection_fault
        .set_handler_fn(general_protection_fault);
    IDT.invalid_opcode.set_handler_fn(invalid_opcode);
    IDT.invalid_tss.set_handler_fn(invalid_tss);
    IDT.machine_check.set_handler_fn(machine_check);
    IDT.non_maskable_interrupt
        .set_handler_fn(non_maskable_interrupt);
    IDT.overflow.set_handler_fn(overflow);
    IDT.page_fault.set_handler_fn(page_fault);
    IDT.security_exception.set_handler_fn(security_exception);
    IDT.segment_not_present.set_handler_fn(segment_not_present);
    IDT.simd_floating_point.set_handler_fn(simd_floating_point);
    IDT.stack_segment_fault.set_handler_fn(stack_segment_fault);
    IDT.virtualization.set_handler_fn(virtualization);
    IDT.vmm_communication_exception
        .set_handler_fn(vmm_communication_exception);
    IDT.x87_floating_point.set_handler_fn(x87_floating_point);

    IDT[0].set_handler_fn(irq11);

    IDT[32].set_handler_fn(irq32);
    IDT[33].set_handler_fn(irq33);
    IDT[34].set_handler_fn(irq34);
    IDT[35].set_handler_fn(irq35);
    IDT[36].set_handler_fn(irq36);
    IDT[37].set_handler_fn(irq37);
    IDT[38].set_handler_fn(irq38);
    IDT[39].set_handler_fn(irq39);
    IDT[40].set_handler_fn(irq40);
    IDT[41].set_handler_fn(irq41);
    IDT[42].set_handler_fn(irq42);
    IDT[43].set_handler_fn(irq43);
    IDT[44].set_handler_fn(irq44);
    IDT[45].set_handler_fn(irq45);
    IDT[46].set_handler_fn(irq46);
    IDT[47].set_handler_fn(irq47);
    IDT[48].set_handler_fn(irq48);
    IDT[49].set_handler_fn(irq49);
    IDT[50].set_handler_fn(irq50);
    IDT[51].set_handler_fn(irq51);
    IDT[52].set_handler_fn(irq52);
    IDT[53].set_handler_fn(irq53);
    IDT[54].set_handler_fn(irq54);
    IDT[55].set_handler_fn(irq55);
    IDT[56].set_handler_fn(irq56);
    IDT[57].set_handler_fn(irq57);
    IDT[58].set_handler_fn(irq58);
    IDT[59].set_handler_fn(irq59);
    IDT[60].set_handler_fn(irq60);
    IDT[61].set_handler_fn(irq61);
    IDT[62].set_handler_fn(irq62);
    IDT[63].set_handler_fn(irq63);
    IDT[64].set_handler_fn(irq64);
    IDT[65].set_handler_fn(irq65);
    IDT[66].set_handler_fn(irq66);
    IDT[67].set_handler_fn(irq67);
    IDT[68].set_handler_fn(irq68);
    IDT[69].set_handler_fn(irq69);
    IDT[70].set_handler_fn(irq70);
    IDT[71].set_handler_fn(irq71);
    IDT[72].set_handler_fn(irq72);
    IDT[73].set_handler_fn(irq73);
    IDT[74].set_handler_fn(irq74);
    IDT[75].set_handler_fn(irq75);
    IDT[76].set_handler_fn(irq76);
    IDT[77].set_handler_fn(irq77);
    IDT[78].set_handler_fn(irq78);
    IDT[79].set_handler_fn(irq79);
    IDT[80].set_handler_fn(irq80);
    IDT[81].set_handler_fn(irq81);
    IDT[82].set_handler_fn(irq82);
    IDT[83].set_handler_fn(irq83);
    IDT[84].set_handler_fn(irq84);
    IDT[85].set_handler_fn(irq85);
    IDT[86].set_handler_fn(irq86);
    IDT[87].set_handler_fn(irq87);
    IDT[88].set_handler_fn(irq88);
    IDT[89].set_handler_fn(irq89);
    IDT[90].set_handler_fn(irq90);
    IDT[91].set_handler_fn(irq91);
    IDT[92].set_handler_fn(irq92);
    IDT[93].set_handler_fn(irq93);
    IDT[94].set_handler_fn(irq94);
    IDT[95].set_handler_fn(irq95);
    IDT[96].set_handler_fn(irq96);
    IDT[97].set_handler_fn(irq97);
    IDT[98].set_handler_fn(irq98);
    IDT[99].set_handler_fn(irq99);
    IDT[100].set_handler_fn(irq100);
    IDT[101].set_handler_fn(irq101);
    IDT[102].set_handler_fn(irq102);
    IDT[103].set_handler_fn(irq103);
    IDT[104].set_handler_fn(irq104);
    IDT[105].set_handler_fn(irq105);
    IDT[106].set_handler_fn(irq106);
    IDT[107].set_handler_fn(irq107);
    IDT[108].set_handler_fn(irq108);
    IDT[109].set_handler_fn(irq109);
    IDT[110].set_handler_fn(irq110);
    IDT[111].set_handler_fn(irq111);
    IDT[112].set_handler_fn(irq112);
    IDT[113].set_handler_fn(irq113);
    IDT[114].set_handler_fn(irq114);
    IDT[115].set_handler_fn(irq115);
    IDT[116].set_handler_fn(irq116);
    IDT[117].set_handler_fn(irq117);
    IDT[118].set_handler_fn(irq118);
    IDT[119].set_handler_fn(irq119);
    IDT[120].set_handler_fn(irq120);
    IDT[121].set_handler_fn(irq121);
    IDT[122].set_handler_fn(irq122);
    IDT[123].set_handler_fn(irq123);
    IDT[124].set_handler_fn(irq124);
    IDT[125].set_handler_fn(irq125);
    IDT[126].set_handler_fn(irq126);
    IDT[127].set_handler_fn(irq127);
    IDT[128].set_handler_fn(irq128);
    IDT[129].set_handler_fn(irq129);
    IDT[130].set_handler_fn(irq130);
    IDT[131].set_handler_fn(irq131);
    IDT[132].set_handler_fn(irq132);
    IDT[133].set_handler_fn(irq133);
    IDT[134].set_handler_fn(irq134);
    IDT[135].set_handler_fn(irq135);
    IDT[136].set_handler_fn(irq136);
    IDT[137].set_handler_fn(irq137);
    IDT[138].set_handler_fn(irq138);
    IDT[139].set_handler_fn(irq139);
    IDT[140].set_handler_fn(irq140);
    IDT[141].set_handler_fn(irq141);
    IDT[142].set_handler_fn(irq142);
    IDT[143].set_handler_fn(irq143);
    IDT[144].set_handler_fn(irq144);
    IDT[145].set_handler_fn(irq145);
    IDT[146].set_handler_fn(irq146);
    IDT[147].set_handler_fn(irq147);
    IDT[148].set_handler_fn(irq148);
    IDT[149].set_handler_fn(irq149);
    IDT[150].set_handler_fn(irq150);
    IDT[151].set_handler_fn(irq151);
    IDT[152].set_handler_fn(irq152);
    IDT[153].set_handler_fn(irq153);
    IDT[154].set_handler_fn(irq154);
    IDT[155].set_handler_fn(irq155);
    IDT[156].set_handler_fn(irq156);
    IDT[157].set_handler_fn(irq157);
    IDT[158].set_handler_fn(irq158);
    IDT[159].set_handler_fn(irq159);
    IDT[160].set_handler_fn(irq160);
    IDT[161].set_handler_fn(irq161);
    IDT[162].set_handler_fn(irq162);
    IDT[163].set_handler_fn(irq163);
    IDT[164].set_handler_fn(irq164);
    IDT[165].set_handler_fn(irq165);
    IDT[166].set_handler_fn(irq166);
    IDT[167].set_handler_fn(irq167);
    IDT[168].set_handler_fn(irq168);
    IDT[169].set_handler_fn(irq169);
    IDT[170].set_handler_fn(irq170);
    IDT[171].set_handler_fn(irq171);
    IDT[172].set_handler_fn(irq172);
    IDT[173].set_handler_fn(irq173);
    IDT[174].set_handler_fn(irq174);
    IDT[175].set_handler_fn(irq175);
    IDT[176].set_handler_fn(irq176);
    IDT[177].set_handler_fn(irq177);
    IDT[178].set_handler_fn(irq178);
    IDT[179].set_handler_fn(irq179);
    IDT[180].set_handler_fn(irq180);
    IDT[181].set_handler_fn(irq181);
    IDT[182].set_handler_fn(irq182);
    IDT[183].set_handler_fn(irq183);
    IDT[184].set_handler_fn(irq184);
    IDT[185].set_handler_fn(irq185);
    IDT[186].set_handler_fn(irq186);
    IDT[187].set_handler_fn(irq187);
    IDT[188].set_handler_fn(irq188);
    IDT[189].set_handler_fn(irq189);
    IDT[190].set_handler_fn(irq190);
    IDT[191].set_handler_fn(irq191);
    IDT[192].set_handler_fn(irq192);
    IDT[193].set_handler_fn(irq193);
    IDT[194].set_handler_fn(irq194);
    IDT[195].set_handler_fn(irq195);
    IDT[196].set_handler_fn(irq196);
    IDT[197].set_handler_fn(irq197);
    IDT[198].set_handler_fn(irq198);
    IDT[199].set_handler_fn(irq199);
    IDT[200].set_handler_fn(irq200);
    IDT[201].set_handler_fn(irq201);
    IDT[202].set_handler_fn(irq202);
    IDT[203].set_handler_fn(irq203);
    IDT[204].set_handler_fn(irq204);
    IDT[205].set_handler_fn(irq205);
    IDT[206].set_handler_fn(irq206);
    IDT[207].set_handler_fn(irq207);
    IDT[208].set_handler_fn(irq208);
    IDT[209].set_handler_fn(irq209);
    IDT[210].set_handler_fn(irq210);
    IDT[211].set_handler_fn(irq211);
    IDT[212].set_handler_fn(irq212);
    IDT[213].set_handler_fn(irq213);
    IDT[214].set_handler_fn(irq214);
    IDT[215].set_handler_fn(irq215);
    IDT[216].set_handler_fn(irq216);
    IDT[217].set_handler_fn(irq217);
    IDT[218].set_handler_fn(irq218);
    IDT[219].set_handler_fn(irq219);
    IDT[220].set_handler_fn(irq220);
    IDT[221].set_handler_fn(irq221);
    IDT[222].set_handler_fn(irq222);
    IDT[223].set_handler_fn(irq223);
    IDT[224].set_handler_fn(irq224);
    IDT[225].set_handler_fn(irq225);
    IDT[226].set_handler_fn(irq226);
    IDT[227].set_handler_fn(irq227);
    IDT[228].set_handler_fn(irq228);
    IDT[229].set_handler_fn(irq229);
    IDT[230].set_handler_fn(irq230);
    IDT[231].set_handler_fn(irq231);
    IDT[232].set_handler_fn(irq232);
    IDT[233].set_handler_fn(irq233);
    IDT[234].set_handler_fn(irq234);
    IDT[235].set_handler_fn(irq235);
    IDT[236].set_handler_fn(irq236);
    IDT[237].set_handler_fn(irq237);
    IDT[238].set_handler_fn(irq238);
    IDT[239].set_handler_fn(irq239);
    IDT[240].set_handler_fn(irq240);
    IDT[241].set_handler_fn(irq241);
    IDT[242].set_handler_fn(irq242);
    IDT[243].set_handler_fn(irq243);
    IDT[244].set_handler_fn(irq244);
    IDT[245].set_handler_fn(irq245);
    IDT[246].set_handler_fn(irq246);
    IDT[247].set_handler_fn(irq247);
    IDT[248].set_handler_fn(irq248);
    IDT[249].set_handler_fn(irq249);
    IDT[250].set_handler_fn(irq250);
    IDT[251].set_handler_fn(irq251);
    IDT[252].set_handler_fn(irq252);
    IDT[253].set_handler_fn(irq253);
    IDT[254].set_handler_fn(irq254);

    IDT[255].set_handler_fn(preemption);

    IDT.load();
}

pub unsafe fn load() {
    IDT.load();
}

extern "x86-interrupt" fn irq11(_stack_frame: InterruptStackFrame) {
    log::debug!("IRQ11");
}

macro_rules! irq_handler {
    ($name:ident, $id:expr) => {
        extern "x86-interrupt" fn $name(_stack_frame: InterruptStackFrame) {
            awkernel_lib::interrupt::eoi(); // End of interrupt.
            awkernel_lib::interrupt::handle_irq($id);
            log::debug!("IRQ{}", $id);
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
        "segment not present: stack_frame = {:?}, error = {error}",
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
