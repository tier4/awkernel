----------------- MODULE exception ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS STACK_SIZE

(*--algorithm exception

variables
    data_abort = FALSE;
    stack_memory = [x \in 0..(STACK_SIZE - 1) |-> <<>>];
    registers = [
        \* general purpose registers
        x0 |-> 0,
        x1 |-> 1,
        x2 |-> 2,
        x3 |-> 3,
        x4 |-> 4,
        x5 |-> 5,
        x6 |-> 6,
        x7 |-> 7,
        x8 |-> 8,
        x9 |-> 9,
        x10 |-> 10,
        x11 |-> 11,
        x12 |-> 12,
        x13 |-> 13,
        x14 |-> 14,
        x15 |-> 15,
        x16 |-> 16,
        x17 |-> 17,
        x18 |-> 18,
        x19 |-> 19,
        x20 |-> 20,
        x21 |-> 21,
        x22 |-> 22,
        x23 |-> 23,
        x24 |-> 24,
        x25 |-> 25,
        x26 |-> 26,
        x27 |-> 27,
        x28 |-> 28,
        x29 |-> 29,
        lr |-> 30, \* equivalent to "x30"

        \* floating-point registers
        q0 |-> 100,
        q1 |-> 101,
        q2 |-> 102,
        q3 |-> 103,
        q4 |-> 104,
        q5 |-> 105,
        q6 |-> 106,
        q7 |-> 107,
        q8 |-> 108,
        q9 |-> 109,
        q10 |-> 110,
        q11 |-> 111,
        q12 |-> 112,
        q13 |-> 113,
        q14 |-> 114,
        q15 |-> 115,
        q16 |-> 116,
        q17 |-> 117,
        q18 |-> 118,
        q19 |-> 119,
        q20 |-> 120,
        q21 |-> 121,
        q22 |-> 122,
        q23 |-> 123,
        q24 |-> 124,
        q25 |-> 125,
        q26 |-> 126,
        q27 |-> 127,
        q28 |-> 128,
        q29 |-> 129,
        q30 |-> 130,
        q31 |-> 131,

        \* system registers
        elr |-> 200,
        esr |-> 201,
        spsr |-> 202,
        fpsr |-> 203,
        fpcr |-> 204,

        \* stack pointer
        sp |-> STACK_SIZE - 1
    ];

macro inc(reg) begin
    registers[reg] := registers[reg] + 1;
end macro;

\* mov dst, src
\*
\* dst = src;
macro mov(dst, src) begin
    registers[dst] := registers[src];
end macro;

\* mrs dst, src
\*
\* dst = src;
macro mrs(dst, src) begin
    registers[dst] := registers[src];
end macro;

\* msr dst, src
\*
\* dst = src;
macro msr(dst, src) begin
    registers[dst] := registers[src];
end macro;

\* add dst, src, imm
\*
\* dst = src + imm;
macro add(dst, src, imm) begin
    registers[dst] := registers[src] + imm;
end macro;

\* sub dst, src, imm
\*
\* dst = src - imm;
macro sub(dst, src, imm) begin
    registers[dst] := registers[src] - imm;
end macro;

procedure interrupt() begin
    start_interrupt:
        either
            skip;
        or
            call CALL_WITH_CONTEXT();
        end either;

    end_interrupt:
        return;
end procedure;

procedure data_abort_exception() begin
    loop_data_abort:
        data_abort := TRUE;
        goto loop_data_abort;
end procedure;

\* str reg1, [reg2, offset]
\*
\* [reg2 + offset] = reg1;
procedure str(reg1, reg2, offset)
variables
    addr
begin
    str0:
        addr := registers[reg2] + offset;
        if addr < 0 \/ addr >= STACK_SIZE then
            call data_abort_exception();
        end if;
    str1:
        stack_memory[addr] := registers[reg1];
        return;
end procedure;

\* str reg1, [reg2, offset]
\*
\* reg1 = [reg2 + offset];
procedure ldr(reg1, reg2, offset)
variables
    addr
begin
    ldr0:
        addr := registers[reg2] + offset;
        if addr < 0 \/ addr >= STACK_SIZE then
            call data_abort_exception();
        end if;
    ldr1:
        registers[reg1] := stack_memory[addr];
        return;
end procedure;

\* str reg1, [reg2], offset
\*
\* [reg2] = reg1;
\* reg2 = reg2 + offset;
procedure str_add(reg1, reg2, offset)
variables
    addr
begin
    str_add0:
        addr := registers[reg2];
        if addr < 0 \/ addr >= STACK_SIZE then
            call data_abort_exception();
        end if;
    str_add1:
        stack_memory[addr] := registers[reg1];
        registers[reg2] := addr + offset;
        return;
end procedure;

\* ldr reg1, [reg2], offset
\*
\* reg1 = [reg2];
\* reg2 = reg2 + offset;
procedure ldr_add(reg1, reg2, offset)
variables
    addr;
begin
    ldr_add0:
        addr := registers[reg2];
        if addr < 0 \/ addr >= STACK_SIZE then
            call data_abort_exception();
        end if;
    ldr_add1:
        registers[reg1] := stack_memory[addr];
    ldr_add2:
        registers[reg2] := addr + offset;
        return;
end procedure;

\* stp reg1, reg2, [reg3, offset]
\*
\* [reg3 + offset] = reg1;
\* [reg3 + offset + 8] = reg2;
procedure stp(reg1, reg2, reg3, offset)
variables
    addr;
begin
    stp0:
        addr := registers[reg3] + offset;
        if addr < 0 \/ addr + 8 >= STACK_SIZE then
            call data_abort_exception();
        end if;
    stp1:
        stack_memory[addr] := registers[reg1];
    stp2:
        stack_memory[addr + 8] := registers[reg2];
        return;
end procedure;

\* ldp reg1, reg2, [reg3, offset],
\*
\* reg1 = [reg3 + offset];
\* reg2 = [reg3 + offset + 8];
procedure ldp(reg1, reg2, reg3, offset)
variables
    addr;
begin
    ldp0:
        addr := registers[reg3] + offset;
        if addr < 0 \/ addr + 8 >= STACK_SIZE then
            call data_abort_exception();
        end if;
    ldp1:
        registers[reg1] := stack_memory[addr];
    ldp2:
        registers[reg2] := stack_memory[addr + 8];
        return;
end procedure;

\* ldp reg1, reg2, [reg3], offset
\*
\* reg1 = [reg3];
\* reg2 = [reg3 + 8];
\* reg3 = reg3 + offset;
procedure ldp_add(reg1, reg2, reg3, offset)
variables
    addr;
begin
    ldp_add0:
        addr := registers[reg3];
        if addr < 0 \/ addr + 8 >= STACK_SIZE then
            call data_abort_exception();
        end if;
    ldp_add1:
        registers[reg1] := stack_memory[addr];
    ldp_add2:
        registers[reg2] := stack_memory[addr + 8];
    ldp_add3:
        registers[reg3] := addr + offset;
        return;
end procedure;

procedure CALL_WITH_CONTEXT()
variables
    ctx_start;
begin
    start_call_with_context:
        ctx_start := registers;

    \* // disable all interrupt
    \* msr     DAIFSet, #0x0f

    \* // handle data abort
    \* mrs     x18, esr_\el
    \* lsr     x18, x18, #27
    \* and     x18, x18, #0b11111
    \*
    \* eor     x18, x18, #0b10000 // x18 == 0b10010 ?
    \* eor     x18, x18, #0b00010
    \*
    \* cbz     x18, data_abort

    \* // Store x0 - x3 on the stack.
    C0: call stp("x0", "x1", "sp", 16 * (-17));
    C1: call stp("x2", "x3", "sp", 16 * (-16));

    \* // Store x31 and ELR.
    C2: mrs("x3", "elr");
    C3: call stp("lr", "x3", "sp", 16 * (-2));

    \*  // x2 is the third argument for the function called through `\handler`.
    C4: mrs("x2", "esr");

    \* // Store SPSR.
    C6: mrs("x3", "spsr");
    C7: call str("x3", "sp", 16 * (-1));

    \* // Make room on the stack for the exception context.
    C5: sub("sp", "sp", 16 * 50);

    \* // enable all interrupt
    \* msr     DAIFClr, #0x0f

    C_INT00: call interrupt();

    \* // x1 is the second argument for the function called through `\handler`.
    C9: add("x1", "sp", 16 * 50);

    C_INT01: call interrupt();

    C10: call exception_store_registers();

    \* // x0 is the first argument for the function called through `\handler`.
    C8: mov("x0", "sp");

    \* // Call `\handler`.
    C11: call handler();

    C_INT02: call interrupt();

    C12: add("x0", "sp", 16 * 48);
    C13: call ldp_add("lr", "x1", "x0", 16);
    C14: call ldr("x2", "x0", 0);

    C_INT03: call interrupt();

    C15: msr("elr", "x1");
    C16: msr("spsr", "x2");

    C_INT04: call interrupt();

    C17: call exception_restore_context();

    end_call_with_context:
        assert ctx_start = registers;
        return;
end procedure;

procedure exception_store_registers() begin
    \* // Store SP.
    S000: call str("x1", "x1", -8);

    S_INT00: call interrupt();

    \* // Store general purpose registers.
    S001: call stp( "x4",  "x5", "x1", 16 * (-15));
    S002: call stp( "x6",  "x7", "x1", 16 * (-14));
    S003: call stp( "x8",  "x9", "x1", 16 * (-13));
    S004: call stp("x10", "x11", "x1", 16 * (-12));
    S005: call stp("x12", "x13", "x1", 16 * (-11));
    S006: call stp("x14", "x15", "x1", 16 * (-10));
    S007: call stp("x16", "x17", "x1", 16 *  (-9));
    S008: call stp("x18", "x19", "x1", 16 *  (-8));
    S009: call stp("x20", "x21", "x1", 16 *  (-7));
    S010: call stp("x22", "x23", "x1", 16 *  (-6));
    S011: call stp("x24", "x25", "x1", 16 *  (-5));
    S012: call stp("x26", "x27", "x1", 16 *  (-4));
    S013: call stp("x28", "x29", "x1", 16 *  (-3));

    S_INT01: call interrupt();

    S14: mov("x3", "sp");

    S_INT02: call interrupt();

    \* // Store all floating-point registers.
    S100: call str_add("q0", "x3", 16);
    S101: call str_add("q1", "x3", 16);
    S102: call str_add("q2", "x3", 16);
    S103: call str_add("q3", "x3", 16);
    S104: call str_add("q4", "x3", 16);
    S105: call str_add("q5", "x3", 16);
    S106: call str_add("q6", "x3", 16);
    S107: call str_add("q7", "x3", 16);
    S108: call str_add("q8", "x3", 16);
    S109: call str_add("q9", "x3", 16);
    S110: call str_add("q10", "x3", 16);
    S111: call str_add("q11", "x3", 16);
    S112: call str_add("q12", "x3", 16);
    S113: call str_add("q13", "x3", 16);
    S114: call str_add("q14", "x3", 16);
    S115: call str_add("q15", "x3", 16);
    S116: call str_add("q16", "x3", 16);
    S117: call str_add("q17", "x3", 16);
    S118: call str_add("q18", "x3", 16);
    S119: call str_add("q19", "x3", 16);
    S120: call str_add("q20", "x3", 16);
    S121: call str_add("q21", "x3", 16);
    S122: call str_add("q22", "x3", 16);
    S123: call str_add("q23", "x3", 16);
    S124: call str_add("q24", "x3", 16);
    S125: call str_add("q25", "x3", 16);
    S126: call str_add("q26", "x3", 16);
    S127: call str_add("q27", "x3", 16);
    S128: call str_add("q28", "x3", 16);
    S129: call str_add("q29", "x3", 16);
    S130: call str_add("q30", "x3", 16);
    S131: call str_add("q31", "x3", 16);

    S_INT03: call interrupt();

    \* // Store FPSR and FPCR registers.
    S200: mrs("x0", "fpsr");
    S201: mrs("x4", "fpcr");
    S202: call stp("x0", "x4", "x3", 0);

    return;
end procedure;

procedure exception_restore_context() begin
    R000: mov("x28", "sp");

    R_INT00: call interrupt();

    R100: call ldr_add("q0", "x28", 16);
    R101: call ldr_add("q1", "x28", 16);
    R102: call ldr_add("q2", "x28", 16);
    R103: call ldr_add("q3", "x28", 16);
    R104: call ldr_add("q4", "x28", 16);
    R105: call ldr_add("q5", "x28", 16);
    R106: call ldr_add("q6", "x28", 16);
    R107: call ldr_add("q7", "x28", 16);
    R108: call ldr_add("q8", "x28", 16);
    R109: call ldr_add("q9", "x28", 16);
    R110: call ldr_add("q10", "x28", 16);
    R111: call ldr_add("q11", "x28", 16);
    R112: call ldr_add("q12", "x28", 16);
    R113: call ldr_add("q13", "x28", 16);
    R114: call ldr_add("q14", "x28", 16);
    R115: call ldr_add("q15", "x28", 16);
    R116: call ldr_add("q16", "x28", 16);
    R117: call ldr_add("q17", "x28", 16);
    R118: call ldr_add("q18", "x28", 16);
    R119: call ldr_add("q19", "x28", 16);
    R120: call ldr_add("q20", "x28", 16);
    R121: call ldr_add("q21", "x28", 16);
    R122: call ldr_add("q22", "x28", 16);
    R123: call ldr_add("q23", "x28", 16);
    R124: call ldr_add("q24", "x28", 16);
    R125: call ldr_add("q25", "x28", 16);
    R126: call ldr_add("q26", "x28", 16);
    R127: call ldr_add("q27", "x28", 16);
    R128: call ldr_add("q28", "x28", 16);
    R129: call ldr_add("q29", "x28", 16);
    R130: call ldr_add("q30", "x28", 16);
    R131: call ldr_add("q31", "x28", 16);

    R_INT01: call interrupt();

    R200: call ldp_add("x0", "x1", "x28", 16); \* Load FPSR and FPCR.

    R201: msr("fpsr", "x0"); \* Restore FPSR
    R202: msr("fpcr", "x1"); \* Restore FPCR.

    R_INT02: call interrupt();

    R300: call ldp_add( "x0",  "x1", "x28", 16);
    R301: call ldp_add( "x2",  "x3", "x28", 16);
    R302: call ldp_add( "x4",  "x5", "x28", 16);
    R303: call ldp_add( "x6",  "x7", "x28", 16);
    R304: call ldp_add( "x8",  "x9", "x28", 16);
    R305: call ldp_add("x10", "x11", "x28", 16);
    R306: call ldp_add("x12", "x13", "x28", 16);
    R307: call ldp_add("x14", "x15", "x28", 16);
    R308: call ldp_add("x16", "x17", "x28", 16);
    R309: call ldp_add("x18", "x19", "x28", 16);
    R310: call ldp_add("x20", "x21", "x28", 16);
    R311: call ldp_add("x22", "x23", "x28", 16);
    R312: call ldp_add("x24", "x25", "x28", 16);
    R313: call ldp_add("x26", "x27", "x28", 16);
    R314: call ldp("x28", "x29", "x28", 0);

    R_INT03: call interrupt();

    R400: add("sp", "sp", 16 * 50); \* Restore SP.

    return;
end procedure;

procedure handler() begin
    H000: inc("x0");
    H001: inc("x1");
    H002: inc("x2");
    H003: inc("x3");
    H004: inc("x4");
    H005: inc("x5");
    H006: inc("x6");
    H007: inc("x7");
    H008: inc("x8");
    H009: inc("x9");
    H010: inc("x10");
    H011: inc("x11");
    H012: inc("x12");
    H013: inc("x13");
    H014: inc("x14");
    H015: inc("x15");
    H016: inc("x16");
    H017: inc("x17");
    H018: inc("x18");
    H019: inc("x19");
    H020: inc("x20");
    H021: inc("x21");
    H022: inc("x22");
    H023: inc("x23");
    H024: inc("x24");
    H025: inc("x25");
    H026: inc("x26");
    H027: inc("x27");
    H028: inc("x28");
    H029: inc("x29");
    H030: inc("lr");

    H_INT00: call interrupt();

    H100: inc("q0");
    H101: inc("q1");
    H102: inc("q2");
    H103: inc("q3");
    H104: inc("q4");
    H105: inc("q5");
    H106: inc("q6");
    H107: inc("q7");
    H108: inc("q8");
    H109: inc("q9");
    H110: inc("q10");
    H111: inc("q11");
    H112: inc("q12");
    H113: inc("q13");
    H114: inc("q14");
    H115: inc("q15");
    H116: inc("q16");
    H117: inc("q17");
    H118: inc("q18");
    H119: inc("q19");
    H120: inc("q20");
    H121: inc("q21");
    H122: inc("q22");
    H123: inc("q23");
    H124: inc("q24");
    H125: inc("q25");
    H126: inc("q26");
    H127: inc("q27");
    H128: inc("q28");
    H129: inc("q29");
    H130: inc("q30");
    H131: inc("q31");

    H_INT01: call interrupt();

    H200: inc("elr");
    H201: inc("spsr");
    H202: inc("fpsr");
    H203: inc("fpcr");

    return;
end procedure;

begin
    start:
        call CALL_WITH_CONTEXT();
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "3126fac" /\ chksum(tla) = "9f7d1874")
\* Procedure variable addr of procedure str at line 152 col 5 changed to addr_
\* Procedure variable addr of procedure ldr at line 169 col 5 changed to addr_l
\* Procedure variable addr of procedure str_add at line 187 col 5 changed to addr_s
\* Procedure variable addr of procedure ldr_add at line 206 col 5 changed to addr_ld
\* Procedure variable addr of procedure stp at line 226 col 5 changed to addr_st
\* Procedure variable addr of procedure ldp at line 246 col 5 changed to addr_ldp
\* Parameter reg1 of procedure str at line 150 col 15 changed to reg1_
\* Parameter reg2 of procedure str at line 150 col 21 changed to reg2_
\* Parameter offset of procedure str at line 150 col 27 changed to offset_
\* Parameter reg1 of procedure ldr at line 167 col 15 changed to reg1_l
\* Parameter reg2 of procedure ldr at line 167 col 21 changed to reg2_l
\* Parameter offset of procedure ldr at line 167 col 27 changed to offset_l
\* Parameter reg1 of procedure str_add at line 185 col 19 changed to reg1_s
\* Parameter reg2 of procedure str_add at line 185 col 25 changed to reg2_s
\* Parameter offset of procedure str_add at line 185 col 31 changed to offset_s
\* Parameter reg1 of procedure ldr_add at line 204 col 19 changed to reg1_ld
\* Parameter reg2 of procedure ldr_add at line 204 col 25 changed to reg2_ld
\* Parameter offset of procedure ldr_add at line 204 col 31 changed to offset_ld
\* Parameter reg1 of procedure stp at line 224 col 15 changed to reg1_st
\* Parameter reg2 of procedure stp at line 224 col 21 changed to reg2_st
\* Parameter reg3 of procedure stp at line 224 col 27 changed to reg3_
\* Parameter offset of procedure stp at line 224 col 33 changed to offset_st
\* Parameter reg1 of procedure ldp at line 244 col 15 changed to reg1_ldp
\* Parameter reg2 of procedure ldp at line 244 col 21 changed to reg2_ldp
\* Parameter reg3 of procedure ldp at line 244 col 27 changed to reg3_l
\* Parameter offset of procedure ldp at line 244 col 33 changed to offset_ldp
CONSTANT defaultInitValue
VARIABLES data_abort, stack_memory, registers, pc, stack, reg1_, reg2_, 
          offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
          offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, 
          reg2_st, reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
          offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start

vars == << data_abort, stack_memory, registers, pc, stack, reg1_, reg2_, 
           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
           offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, 
           reg2_st, reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

Init == (* Global variables *)
        /\ data_abort = FALSE
        /\ stack_memory = [x \in 0..(STACK_SIZE - 1) |-> <<>>]
        /\ registers =             [
                       
                           x0 |-> 0,
                           x1 |-> 1,
                           x2 |-> 2,
                           x3 |-> 3,
                           x4 |-> 4,
                           x5 |-> 5,
                           x6 |-> 6,
                           x7 |-> 7,
                           x8 |-> 8,
                           x9 |-> 9,
                           x10 |-> 10,
                           x11 |-> 11,
                           x12 |-> 12,
                           x13 |-> 13,
                           x14 |-> 14,
                           x15 |-> 15,
                           x16 |-> 16,
                           x17 |-> 17,
                           x18 |-> 18,
                           x19 |-> 19,
                           x20 |-> 20,
                           x21 |-> 21,
                           x22 |-> 22,
                           x23 |-> 23,
                           x24 |-> 24,
                           x25 |-> 25,
                           x26 |-> 26,
                           x27 |-> 27,
                           x28 |-> 28,
                           x29 |-> 29,
                           lr |-> 30,
                       
                       
                           q0 |-> 100,
                           q1 |-> 101,
                           q2 |-> 102,
                           q3 |-> 103,
                           q4 |-> 104,
                           q5 |-> 105,
                           q6 |-> 106,
                           q7 |-> 107,
                           q8 |-> 108,
                           q9 |-> 109,
                           q10 |-> 110,
                           q11 |-> 111,
                           q12 |-> 112,
                           q13 |-> 113,
                           q14 |-> 114,
                           q15 |-> 115,
                           q16 |-> 116,
                           q17 |-> 117,
                           q18 |-> 118,
                           q19 |-> 119,
                           q20 |-> 120,
                           q21 |-> 121,
                           q22 |-> 122,
                           q23 |-> 123,
                           q24 |-> 124,
                           q25 |-> 125,
                           q26 |-> 126,
                           q27 |-> 127,
                           q28 |-> 128,
                           q29 |-> 129,
                           q30 |-> 130,
                           q31 |-> 131,
                       
                       
                           elr |-> 200,
                           esr |-> 201,
                           spsr |-> 202,
                           fpsr |-> 203,
                           fpcr |-> 204,
                       
                       
                           sp |-> STACK_SIZE - 1
                       ]
        (* Procedure str *)
        /\ reg1_ = defaultInitValue
        /\ reg2_ = defaultInitValue
        /\ offset_ = defaultInitValue
        /\ addr_ = defaultInitValue
        (* Procedure ldr *)
        /\ reg1_l = defaultInitValue
        /\ reg2_l = defaultInitValue
        /\ offset_l = defaultInitValue
        /\ addr_l = defaultInitValue
        (* Procedure str_add *)
        /\ reg1_s = defaultInitValue
        /\ reg2_s = defaultInitValue
        /\ offset_s = defaultInitValue
        /\ addr_s = defaultInitValue
        (* Procedure ldr_add *)
        /\ reg1_ld = defaultInitValue
        /\ reg2_ld = defaultInitValue
        /\ offset_ld = defaultInitValue
        /\ addr_ld = defaultInitValue
        (* Procedure stp *)
        /\ reg1_st = defaultInitValue
        /\ reg2_st = defaultInitValue
        /\ reg3_ = defaultInitValue
        /\ offset_st = defaultInitValue
        /\ addr_st = defaultInitValue
        (* Procedure ldp *)
        /\ reg1_ldp = defaultInitValue
        /\ reg2_ldp = defaultInitValue
        /\ reg3_l = defaultInitValue
        /\ offset_ldp = defaultInitValue
        /\ addr_ldp = defaultInitValue
        (* Procedure ldp_add *)
        /\ reg1 = defaultInitValue
        /\ reg2 = defaultInitValue
        /\ reg3 = defaultInitValue
        /\ offset = defaultInitValue
        /\ addr = defaultInitValue
        (* Procedure CALL_WITH_CONTEXT *)
        /\ ctx_start = defaultInitValue
        /\ stack = << >>
        /\ pc = "start"

start_interrupt == /\ pc = "start_interrupt"
                   /\ \/ /\ TRUE
                         /\ pc' = "end_interrupt"
                         /\ UNCHANGED <<stack, ctx_start>>
                      \/ /\ stack' = << [ procedure |->  "CALL_WITH_CONTEXT",
                                          pc        |->  "end_interrupt",
                                          ctx_start |->  ctx_start ] >>
                                      \o stack
                         /\ ctx_start' = defaultInitValue
                         /\ pc' = "start_call_with_context"
                   /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, 
                                   reg2_, offset_, addr_, reg1_l, reg2_l, 
                                   offset_l, addr_l, reg1_s, reg2_s, offset_s, 
                                   addr_s, reg1_ld, reg2_ld, offset_ld, 
                                   addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                                   addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                                   offset_ldp, addr_ldp, reg1, reg2, reg3, 
                                   offset, addr >>

end_interrupt == /\ pc = "end_interrupt"
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, 
                                 reg2_, offset_, addr_, reg1_l, reg2_l, 
                                 offset_l, addr_l, reg1_s, reg2_s, offset_s, 
                                 addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                                 reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                                 reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                                 addr_ldp, reg1, reg2, reg3, offset, addr, 
                                 ctx_start >>

interrupt == start_interrupt \/ end_interrupt

loop_data_abort == /\ pc = "loop_data_abort"
                   /\ data_abort' = TRUE
                   /\ pc' = "loop_data_abort"
                   /\ UNCHANGED << stack_memory, registers, stack, reg1_, 
                                   reg2_, offset_, addr_, reg1_l, reg2_l, 
                                   offset_l, addr_l, reg1_s, reg2_s, offset_s, 
                                   addr_s, reg1_ld, reg2_ld, offset_ld, 
                                   addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                                   addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                                   offset_ldp, addr_ldp, reg1, reg2, reg3, 
                                   offset, addr, ctx_start >>

data_abort_exception == loop_data_abort

str0 == /\ pc = "str0"
        /\ addr_' = registers[reg2_] + offset_
        /\ IF addr_' < 0 \/ addr_' >= STACK_SIZE
              THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                    pc        |->  "str1" ] >>
                                \o stack
                   /\ pc' = "loop_data_abort"
              ELSE /\ pc' = "str1"
                   /\ stack' = stack
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

str1 == /\ pc = "str1"
        /\ stack_memory' = [stack_memory EXCEPT ![addr_] = registers[reg1_]]
        /\ pc' = Head(stack).pc
        /\ addr_' = Head(stack).addr_
        /\ reg1_' = Head(stack).reg1_
        /\ reg2_' = Head(stack).reg2_
        /\ offset_' = Head(stack).offset_
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, registers, reg1_l, reg2_l, offset_l, 
                        addr_l, reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                        reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                        offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

str == str0 \/ str1

ldr0 == /\ pc = "ldr0"
        /\ addr_l' = registers[reg2_l] + offset_l
        /\ IF addr_l' < 0 \/ addr_l' >= STACK_SIZE
              THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                    pc        |->  "ldr1" ] >>
                                \o stack
                   /\ pc' = "loop_data_abort"
              ELSE /\ pc' = "ldr1"
                   /\ stack' = stack
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

ldr1 == /\ pc = "ldr1"
        /\ registers' = [registers EXCEPT ![reg1_l] = stack_memory[addr_l]]
        /\ pc' = Head(stack).pc
        /\ addr_l' = Head(stack).addr_l
        /\ reg1_l' = Head(stack).reg1_l
        /\ reg2_l' = Head(stack).reg2_l
        /\ offset_l' = Head(stack).offset_l
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, addr_, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

ldr == ldr0 \/ ldr1

str_add0 == /\ pc = "str_add0"
            /\ addr_s' = registers[reg2_s]
            /\ IF addr_s' < 0 \/ addr_s' >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "str_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "str_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_start >>

str_add1 == /\ pc = "str_add1"
            /\ stack_memory' = [stack_memory EXCEPT ![addr_s] = registers[reg1_s]]
            /\ registers' = [registers EXCEPT ![reg2_s] = addr_s + offset_s]
            /\ pc' = Head(stack).pc
            /\ addr_s' = Head(stack).addr_s
            /\ reg1_s' = Head(stack).reg1_s
            /\ reg2_s' = Head(stack).reg2_s
            /\ offset_s' = Head(stack).offset_s
            /\ stack' = Tail(stack)
            /\ UNCHANGED << data_abort, reg1_, reg2_, offset_, addr_, reg1_l, 
                            reg2_l, offset_l, addr_l, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_start >>

str_add == str_add0 \/ str_add1

ldr_add0 == /\ pc = "ldr_add0"
            /\ addr_ld' = registers[reg2_ld]
            /\ IF addr_ld' < 0 \/ addr_ld' >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "ldr_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "ldr_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, reg1_st, reg2_st, reg3_, offset_st, 
                            addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                            addr_ldp, reg1, reg2, reg3, offset, addr, 
                            ctx_start >>

ldr_add1 == /\ pc = "ldr_add1"
            /\ registers' = [registers EXCEPT ![reg1_ld] = stack_memory[addr_ld]]
            /\ pc' = "ldr_add2"
            /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_start >>

ldr_add2 == /\ pc = "ldr_add2"
            /\ registers' = [registers EXCEPT ![reg2_ld] = addr_ld + offset_ld]
            /\ pc' = Head(stack).pc
            /\ addr_ld' = Head(stack).addr_ld
            /\ reg1_ld' = Head(stack).reg1_ld
            /\ reg2_ld' = Head(stack).reg2_ld
            /\ offset_ld' = Head(stack).offset_ld
            /\ stack' = Tail(stack)
            /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, offset_s, addr_s, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_start >>

ldr_add == ldr_add0 \/ ldr_add1 \/ ldr_add2

stp0 == /\ pc = "stp0"
        /\ addr_st' = registers[reg3_] + offset_st
        /\ IF addr_st' < 0 \/ addr_st' + 8 >= STACK_SIZE
              THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                    pc        |->  "stp1" ] >>
                                \o stack
                   /\ pc' = "loop_data_abort"
              ELSE /\ pc' = "stp1"
                   /\ stack' = stack
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

stp1 == /\ pc = "stp1"
        /\ stack_memory' = [stack_memory EXCEPT ![addr_st] = registers[reg1_st]]
        /\ pc' = "stp2"
        /\ UNCHANGED << data_abort, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

stp2 == /\ pc = "stp2"
        /\ stack_memory' = [stack_memory EXCEPT ![addr_st + 8] = registers[reg2_st]]
        /\ pc' = Head(stack).pc
        /\ addr_st' = Head(stack).addr_st
        /\ reg1_st' = Head(stack).reg1_st
        /\ reg2_st' = Head(stack).reg2_st
        /\ reg3_' = Head(stack).reg3_
        /\ offset_st' = Head(stack).offset_st
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

stp == stp0 \/ stp1 \/ stp2

ldp0 == /\ pc = "ldp0"
        /\ addr_ldp' = registers[reg3_l] + offset_ldp
        /\ IF addr_ldp' < 0 \/ addr_ldp' + 8 >= STACK_SIZE
              THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                    pc        |->  "ldp1" ] >>
                                \o stack
                   /\ pc' = "loop_data_abort"
              ELSE /\ pc' = "ldp1"
                   /\ stack' = stack
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

ldp1 == /\ pc = "ldp1"
        /\ registers' = [registers EXCEPT ![reg1_ldp] = stack_memory[addr_ldp]]
        /\ pc' = "ldp2"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

ldp2 == /\ pc = "ldp2"
        /\ registers' = [registers EXCEPT ![reg2_ldp] = stack_memory[addr_ldp + 8]]
        /\ pc' = Head(stack).pc
        /\ addr_ldp' = Head(stack).addr_ldp
        /\ reg1_ldp' = Head(stack).reg1_ldp
        /\ reg2_ldp' = Head(stack).reg2_ldp
        /\ reg3_l' = Head(stack).reg3_l
        /\ offset_ldp' = Head(stack).offset_ldp
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                        reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

ldp == ldp0 \/ ldp1 \/ ldp2

ldp_add0 == /\ pc = "ldp_add0"
            /\ addr' = registers[reg3]
            /\ IF addr' < 0 \/ addr' + 8 >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "ldp_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "ldp_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            ctx_start >>

ldp_add1 == /\ pc = "ldp_add1"
            /\ registers' = [registers EXCEPT ![reg1] = stack_memory[addr]]
            /\ pc' = "ldp_add2"
            /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_start >>

ldp_add2 == /\ pc = "ldp_add2"
            /\ registers' = [registers EXCEPT ![reg2] = stack_memory[addr + 8]]
            /\ pc' = "ldp_add3"
            /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_start >>

ldp_add3 == /\ pc = "ldp_add3"
            /\ registers' = [registers EXCEPT ![reg3] = addr + offset]
            /\ pc' = Head(stack).pc
            /\ addr' = Head(stack).addr
            /\ reg1' = Head(stack).reg1
            /\ reg2' = Head(stack).reg2
            /\ reg3' = Head(stack).reg3
            /\ offset' = Head(stack).offset
            /\ stack' = Tail(stack)
            /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, ctx_start >>

ldp_add == ldp_add0 \/ ldp_add1 \/ ldp_add2 \/ ldp_add3

start_call_with_context == /\ pc = "start_call_with_context"
                           /\ ctx_start' = registers
                           /\ pc' = "C0"
                           /\ UNCHANGED << data_abort, stack_memory, registers, 
                                           stack, reg1_, reg2_, offset_, addr_, 
                                           reg1_l, reg2_l, offset_l, addr_l, 
                                           reg1_s, reg2_s, offset_s, addr_s, 
                                           reg1_ld, reg2_ld, offset_ld, 
                                           addr_ld, reg1_st, reg2_st, reg3_, 
                                           offset_st, addr_st, reg1_ldp, 
                                           reg2_ldp, reg3_l, offset_ldp, 
                                           addr_ldp, reg1, reg2, reg3, offset, 
                                           addr >>

C0 == /\ pc = "C0"
      /\ /\ offset_st' = 16 * (-17)
         /\ reg1_st' = "x0"
         /\ reg2_st' = "x1"
         /\ reg3_' = "sp"
         /\ stack' = << [ procedure |->  "stp",
                          pc        |->  "C1",
                          addr_st   |->  addr_st,
                          reg1_st   |->  reg1_st,
                          reg2_st   |->  reg2_st,
                          reg3_     |->  reg3_,
                          offset_st |->  offset_st ] >>
                      \o stack
      /\ addr_st' = defaultInitValue
      /\ pc' = "stp0"
      /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                      offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                      reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                      addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                      addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

C1 == /\ pc = "C1"
      /\ /\ offset_st' = 16 * (-16)
         /\ reg1_st' = "x2"
         /\ reg2_st' = "x3"
         /\ reg3_' = "sp"
         /\ stack' = << [ procedure |->  "stp",
                          pc        |->  "C2",
                          addr_st   |->  addr_st,
                          reg1_st   |->  reg1_st,
                          reg2_st   |->  reg2_st,
                          reg3_     |->  reg3_,
                          offset_st |->  offset_st ] >>
                      \o stack
      /\ addr_st' = defaultInitValue
      /\ pc' = "stp0"
      /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                      offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                      reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                      addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                      addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

C2 == /\ pc = "C2"
      /\ registers' = [registers EXCEPT !["x3"] = registers["elr"]]
      /\ pc' = "C3"
      /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                      addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                      offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                      reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                      reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                      offset, addr, ctx_start >>

C3 == /\ pc = "C3"
      /\ /\ offset_st' = 16 * (-2)
         /\ reg1_st' = "lr"
         /\ reg2_st' = "x3"
         /\ reg3_' = "sp"
         /\ stack' = << [ procedure |->  "stp",
                          pc        |->  "C4",
                          addr_st   |->  addr_st,
                          reg1_st   |->  reg1_st,
                          reg2_st   |->  reg2_st,
                          reg3_     |->  reg3_,
                          offset_st |->  offset_st ] >>
                      \o stack
      /\ addr_st' = defaultInitValue
      /\ pc' = "stp0"
      /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                      offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                      reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                      addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                      addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

C4 == /\ pc = "C4"
      /\ registers' = [registers EXCEPT !["x2"] = registers["esr"]]
      /\ pc' = "C6"
      /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                      addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                      offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                      reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                      reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                      offset, addr, ctx_start >>

C6 == /\ pc = "C6"
      /\ registers' = [registers EXCEPT !["x3"] = registers["spsr"]]
      /\ pc' = "C7"
      /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                      addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                      offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                      reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                      reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                      offset, addr, ctx_start >>

C7 == /\ pc = "C7"
      /\ /\ offset_' = 16 * (-1)
         /\ reg1_' = "x3"
         /\ reg2_' = "sp"
         /\ stack' = << [ procedure |->  "str",
                          pc        |->  "C5",
                          addr_     |->  addr_,
                          reg1_     |->  reg1_,
                          reg2_     |->  reg2_,
                          offset_   |->  offset_ ] >>
                      \o stack
      /\ addr_' = defaultInitValue
      /\ pc' = "str0"
      /\ UNCHANGED << data_abort, stack_memory, registers, reg1_l, reg2_l, 
                      offset_l, addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                      reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                      reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                      offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                      ctx_start >>

C5 == /\ pc = "C5"
      /\ registers' = [registers EXCEPT !["sp"] = registers["sp"] - (16 * 50)]
      /\ pc' = "C_INT00"
      /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                      addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                      offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                      reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                      reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                      offset, addr, ctx_start >>

C_INT00 == /\ pc = "C_INT00"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C9" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

C9 == /\ pc = "C9"
      /\ registers' = [registers EXCEPT !["x1"] = registers["sp"] + (16 * 50)]
      /\ pc' = "C_INT01"
      /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                      addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                      offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                      reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                      reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                      offset, addr, ctx_start >>

C_INT01 == /\ pc = "C_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C10" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

C10 == /\ pc = "C10"
       /\ stack' = << [ procedure |->  "exception_store_registers",
                        pc        |->  "C8" ] >>
                    \o stack
       /\ pc' = "S000"
       /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                       offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                       reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                       offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

C8 == /\ pc = "C8"
      /\ registers' = [registers EXCEPT !["x0"] = registers["sp"]]
      /\ pc' = "C11"
      /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                      addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                      offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                      reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                      reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                      offset, addr, ctx_start >>

C11 == /\ pc = "C11"
       /\ stack' = << [ procedure |->  "handler",
                        pc        |->  "C_INT02" ] >>
                    \o stack
       /\ pc' = "H000"
       /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                       offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                       reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                       offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

C_INT02 == /\ pc = "C_INT02"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C12" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

C12 == /\ pc = "C12"
       /\ registers' = [registers EXCEPT !["x0"] = registers["sp"] + (16 * 48)]
       /\ pc' = "C13"
       /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                       reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                       reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                       reg3, offset, addr, ctx_start >>

C13 == /\ pc = "C13"
       /\ /\ offset' = 16
          /\ reg1' = "lr"
          /\ reg2' = "x1"
          /\ reg3' = "x0"
          /\ stack' = << [ procedure |->  "ldp_add",
                           pc        |->  "C14",
                           addr      |->  addr,
                           reg1      |->  reg1,
                           reg2      |->  reg2,
                           reg3      |->  reg3,
                           offset    |->  offset ] >>
                       \o stack
       /\ addr' = defaultInitValue
       /\ pc' = "ldp_add0"
       /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                       offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                       reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                       offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, ctx_start >>

C14 == /\ pc = "C14"
       /\ /\ offset_l' = 0
          /\ reg1_l' = "x2"
          /\ reg2_l' = "x0"
          /\ stack' = << [ procedure |->  "ldr",
                           pc        |->  "C_INT03",
                           addr_l    |->  addr_l,
                           reg1_l    |->  reg1_l,
                           reg2_l    |->  reg2_l,
                           offset_l  |->  offset_l ] >>
                       \o stack
       /\ addr_l' = defaultInitValue
       /\ pc' = "ldr0"
       /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                       offset_, addr_, reg1_s, reg2_s, offset_s, addr_s, 
                       reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                       reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_start >>

C_INT03 == /\ pc = "C_INT03"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C15" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

C15 == /\ pc = "C15"
       /\ registers' = [registers EXCEPT !["elr"] = registers["x1"]]
       /\ pc' = "C16"
       /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                       reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                       reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                       reg3, offset, addr, ctx_start >>

C16 == /\ pc = "C16"
       /\ registers' = [registers EXCEPT !["spsr"] = registers["x2"]]
       /\ pc' = "C_INT04"
       /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                       reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                       reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                       reg3, offset, addr, ctx_start >>

C_INT04 == /\ pc = "C_INT04"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C17" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

C17 == /\ pc = "C17"
       /\ stack' = << [ procedure |->  "exception_restore_context",
                        pc        |->  "end_call_with_context" ] >>
                    \o stack
       /\ pc' = "R000"
       /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                       offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                       reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                       offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_start >>

end_call_with_context == /\ pc = "end_call_with_context"
                         /\ Assert(ctx_start = registers, 
                                   "Failure of assertion at line 355, column 9.")
                         /\ pc' = Head(stack).pc
                         /\ ctx_start' = Head(stack).ctx_start
                         /\ stack' = Tail(stack)
                         /\ UNCHANGED << data_abort, stack_memory, registers, 
                                         reg1_, reg2_, offset_, addr_, reg1_l, 
                                         reg2_l, offset_l, addr_l, reg1_s, 
                                         reg2_s, offset_s, addr_s, reg1_ld, 
                                         reg2_ld, offset_ld, addr_ld, reg1_st, 
                                         reg2_st, reg3_, offset_st, addr_st, 
                                         reg1_ldp, reg2_ldp, reg3_l, 
                                         offset_ldp, addr_ldp, reg1, reg2, 
                                         reg3, offset, addr >>

CALL_WITH_CONTEXT == start_call_with_context \/ C0 \/ C1 \/ C2 \/ C3 \/ C4
                        \/ C6 \/ C7 \/ C5 \/ C_INT00 \/ C9 \/ C_INT01
                        \/ C10 \/ C8 \/ C11 \/ C_INT02 \/ C12 \/ C13 \/ C14
                        \/ C_INT03 \/ C15 \/ C16 \/ C_INT04 \/ C17
                        \/ end_call_with_context

S000 == /\ pc = "S000"
        /\ /\ offset_' = -8
           /\ reg1_' = "x1"
           /\ reg2_' = "x1"
           /\ stack' = << [ procedure |->  "str",
                            pc        |->  "S_INT00",
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "str0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S_INT00 == /\ pc = "S_INT00"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "S001" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

S001 == /\ pc = "S001"
        /\ /\ offset_st' = 16 * (-15)
           /\ reg1_st' = "x4"
           /\ reg2_st' = "x5"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S002",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S002 == /\ pc = "S002"
        /\ /\ offset_st' = 16 * (-14)
           /\ reg1_st' = "x6"
           /\ reg2_st' = "x7"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S003",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S003 == /\ pc = "S003"
        /\ /\ offset_st' = 16 * (-13)
           /\ reg1_st' = "x8"
           /\ reg2_st' = "x9"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S004",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S004 == /\ pc = "S004"
        /\ /\ offset_st' = 16 * (-12)
           /\ reg1_st' = "x10"
           /\ reg2_st' = "x11"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S005",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S005 == /\ pc = "S005"
        /\ /\ offset_st' = 16 * (-11)
           /\ reg1_st' = "x12"
           /\ reg2_st' = "x13"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S006",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S006 == /\ pc = "S006"
        /\ /\ offset_st' = 16 * (-10)
           /\ reg1_st' = "x14"
           /\ reg2_st' = "x15"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S007",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S007 == /\ pc = "S007"
        /\ /\ offset_st' = 16 *  (-9)
           /\ reg1_st' = "x16"
           /\ reg2_st' = "x17"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S008",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S008 == /\ pc = "S008"
        /\ /\ offset_st' = 16 *  (-8)
           /\ reg1_st' = "x18"
           /\ reg2_st' = "x19"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S009",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S009 == /\ pc = "S009"
        /\ /\ offset_st' = 16 *  (-7)
           /\ reg1_st' = "x20"
           /\ reg2_st' = "x21"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S010",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S010 == /\ pc = "S010"
        /\ /\ offset_st' = 16 *  (-6)
           /\ reg1_st' = "x22"
           /\ reg2_st' = "x23"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S011",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S011 == /\ pc = "S011"
        /\ /\ offset_st' = 16 *  (-5)
           /\ reg1_st' = "x24"
           /\ reg2_st' = "x25"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S012",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S012 == /\ pc = "S012"
        /\ /\ offset_st' = 16 *  (-4)
           /\ reg1_st' = "x26"
           /\ reg2_st' = "x27"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S013",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S013 == /\ pc = "S013"
        /\ /\ offset_st' = 16 *  (-3)
           /\ reg1_st' = "x28"
           /\ reg2_st' = "x29"
           /\ reg3_' = "x1"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S_INT01",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S_INT01 == /\ pc = "S_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "S14" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

S14 == /\ pc = "S14"
       /\ registers' = [registers EXCEPT !["x3"] = registers["sp"]]
       /\ pc' = "S_INT02"
       /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                       reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                       reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                       reg3, offset, addr, ctx_start >>

S_INT02 == /\ pc = "S_INT02"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "S100" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

S100 == /\ pc = "S100"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q0"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S101",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S101 == /\ pc = "S101"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q1"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S102",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S102 == /\ pc = "S102"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q2"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S103",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S103 == /\ pc = "S103"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q3"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S104",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S104 == /\ pc = "S104"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q4"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S105",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S105 == /\ pc = "S105"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q5"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S106",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S106 == /\ pc = "S106"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q6"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S107",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S107 == /\ pc = "S107"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q7"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S108",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S108 == /\ pc = "S108"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q8"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S109",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S109 == /\ pc = "S109"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q9"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S110",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S110 == /\ pc = "S110"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q10"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S111",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S111 == /\ pc = "S111"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q11"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S112",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S112 == /\ pc = "S112"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q12"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S113",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S113 == /\ pc = "S113"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q13"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S114",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S114 == /\ pc = "S114"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q14"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S115",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S115 == /\ pc = "S115"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q15"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S116",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S116 == /\ pc = "S116"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q16"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S117",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S117 == /\ pc = "S117"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q17"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S118",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S118 == /\ pc = "S118"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q18"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S119",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S119 == /\ pc = "S119"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q19"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S120",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S120 == /\ pc = "S120"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q20"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S121",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S121 == /\ pc = "S121"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q21"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S122",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S122 == /\ pc = "S122"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q22"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S123",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S123 == /\ pc = "S123"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q23"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S124",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S124 == /\ pc = "S124"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q24"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S125",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S125 == /\ pc = "S125"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q25"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S126",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S126 == /\ pc = "S126"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q26"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S127",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S127 == /\ pc = "S127"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q27"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S128",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S128 == /\ pc = "S128"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q28"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S129",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S129 == /\ pc = "S129"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q29"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S130",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S130 == /\ pc = "S130"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q30"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S131",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S131 == /\ pc = "S131"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "q31"
           /\ reg2_s' = "x3"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S_INT03",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

S_INT03 == /\ pc = "S_INT03"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "S200" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

S200 == /\ pc = "S200"
        /\ registers' = [registers EXCEPT !["x0"] = registers["fpsr"]]
        /\ pc' = "S201"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

S201 == /\ pc = "S201"
        /\ registers' = [registers EXCEPT !["x4"] = registers["fpcr"]]
        /\ pc' = "S202"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

S202 == /\ pc = "S202"
        /\ /\ offset_st' = 0
           /\ reg1_st' = "x0"
           /\ reg2_st' = "x4"
           /\ reg3_' = "x3"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  Head(stack).pc,
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o Tail(stack)
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

exception_store_registers == S000 \/ S_INT00 \/ S001 \/ S002 \/ S003
                                \/ S004 \/ S005 \/ S006 \/ S007 \/ S008
                                \/ S009 \/ S010 \/ S011 \/ S012 \/ S013
                                \/ S_INT01 \/ S14 \/ S_INT02 \/ S100
                                \/ S101 \/ S102 \/ S103 \/ S104 \/ S105
                                \/ S106 \/ S107 \/ S108 \/ S109 \/ S110
                                \/ S111 \/ S112 \/ S113 \/ S114 \/ S115
                                \/ S116 \/ S117 \/ S118 \/ S119 \/ S120
                                \/ S121 \/ S122 \/ S123 \/ S124 \/ S125
                                \/ S126 \/ S127 \/ S128 \/ S129 \/ S130
                                \/ S131 \/ S_INT03 \/ S200 \/ S201 \/ S202

R000 == /\ pc = "R000"
        /\ registers' = [registers EXCEPT !["x28"] = registers["sp"]]
        /\ pc' = "R_INT00"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

R_INT00 == /\ pc = "R_INT00"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "R100" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

R100 == /\ pc = "R100"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q0"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R101",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R101 == /\ pc = "R101"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q1"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R102",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R102 == /\ pc = "R102"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q2"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R103",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R103 == /\ pc = "R103"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q3"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R104",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R104 == /\ pc = "R104"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q4"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R105",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R105 == /\ pc = "R105"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q5"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R106",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R106 == /\ pc = "R106"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q6"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R107",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R107 == /\ pc = "R107"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q7"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R108",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R108 == /\ pc = "R108"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q8"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R109",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R109 == /\ pc = "R109"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q9"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R110",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R110 == /\ pc = "R110"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q10"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R111",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R111 == /\ pc = "R111"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q11"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R112",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R112 == /\ pc = "R112"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q12"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R113",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R113 == /\ pc = "R113"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q13"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R114",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R114 == /\ pc = "R114"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q14"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R115",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R115 == /\ pc = "R115"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q15"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R116",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R116 == /\ pc = "R116"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q16"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R117",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R117 == /\ pc = "R117"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q17"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R118",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R118 == /\ pc = "R118"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q18"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R119",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R119 == /\ pc = "R119"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q19"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R120",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R120 == /\ pc = "R120"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q20"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R121",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R121 == /\ pc = "R121"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q21"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R122",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R122 == /\ pc = "R122"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q22"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R123",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R123 == /\ pc = "R123"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q23"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R124",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R124 == /\ pc = "R124"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q24"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R125",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R125 == /\ pc = "R125"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q25"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R126",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R126 == /\ pc = "R126"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q26"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R127",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R127 == /\ pc = "R127"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q27"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R128",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R128 == /\ pc = "R128"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q28"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R129",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R129 == /\ pc = "R129"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q29"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R130",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R130 == /\ pc = "R130"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q30"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R131",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R131 == /\ pc = "R131"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "q31"
           /\ reg2_ld' = "x28"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R_INT01",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

R_INT01 == /\ pc = "R_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "R200" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

R200 == /\ pc = "R200"
        /\ /\ offset' = 16
           /\ reg1' = "x0"
           /\ reg2' = "x1"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R201",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R201 == /\ pc = "R201"
        /\ registers' = [registers EXCEPT !["fpsr"] = registers["x0"]]
        /\ pc' = "R202"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

R202 == /\ pc = "R202"
        /\ registers' = [registers EXCEPT !["fpcr"] = registers["x1"]]
        /\ pc' = "R_INT02"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

R_INT02 == /\ pc = "R_INT02"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "R300" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

R300 == /\ pc = "R300"
        /\ /\ offset' = 16
           /\ reg1' = "x0"
           /\ reg2' = "x1"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R301",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R301 == /\ pc = "R301"
        /\ /\ offset' = 16
           /\ reg1' = "x2"
           /\ reg2' = "x3"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R302",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R302 == /\ pc = "R302"
        /\ /\ offset' = 16
           /\ reg1' = "x4"
           /\ reg2' = "x5"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R303",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R303 == /\ pc = "R303"
        /\ /\ offset' = 16
           /\ reg1' = "x6"
           /\ reg2' = "x7"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R304",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R304 == /\ pc = "R304"
        /\ /\ offset' = 16
           /\ reg1' = "x8"
           /\ reg2' = "x9"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R305",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R305 == /\ pc = "R305"
        /\ /\ offset' = 16
           /\ reg1' = "x10"
           /\ reg2' = "x11"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R306",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R306 == /\ pc = "R306"
        /\ /\ offset' = 16
           /\ reg1' = "x12"
           /\ reg2' = "x13"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R307",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R307 == /\ pc = "R307"
        /\ /\ offset' = 16
           /\ reg1' = "x14"
           /\ reg2' = "x15"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R308",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R308 == /\ pc = "R308"
        /\ /\ offset' = 16
           /\ reg1' = "x16"
           /\ reg2' = "x17"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R309",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R309 == /\ pc = "R309"
        /\ /\ offset' = 16
           /\ reg1' = "x18"
           /\ reg2' = "x19"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R310",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R310 == /\ pc = "R310"
        /\ /\ offset' = 16
           /\ reg1' = "x20"
           /\ reg2' = "x21"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R311",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R311 == /\ pc = "R311"
        /\ /\ offset' = 16
           /\ reg1' = "x22"
           /\ reg2' = "x23"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R312",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R312 == /\ pc = "R312"
        /\ /\ offset' = 16
           /\ reg1' = "x24"
           /\ reg2' = "x25"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R313",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R313 == /\ pc = "R313"
        /\ /\ offset' = 16
           /\ reg1' = "x26"
           /\ reg2' = "x27"
           /\ reg3' = "x28"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R314",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, ctx_start >>

R314 == /\ pc = "R314"
        /\ /\ offset_ldp' = 0
           /\ reg1_ldp' = "x28"
           /\ reg2_ldp' = "x29"
           /\ reg3_l' = "x28"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R_INT03",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1, reg2, reg3, offset, addr, ctx_start >>

R_INT03 == /\ pc = "R_INT03"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "R400" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

R400 == /\ pc = "R400"
        /\ registers' = [registers EXCEPT !["sp"] = registers["sp"] + (16 * 50)]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                        reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                        reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

exception_restore_context == R000 \/ R_INT00 \/ R100 \/ R101 \/ R102
                                \/ R103 \/ R104 \/ R105 \/ R106 \/ R107
                                \/ R108 \/ R109 \/ R110 \/ R111 \/ R112
                                \/ R113 \/ R114 \/ R115 \/ R116 \/ R117
                                \/ R118 \/ R119 \/ R120 \/ R121 \/ R122
                                \/ R123 \/ R124 \/ R125 \/ R126 \/ R127
                                \/ R128 \/ R129 \/ R130 \/ R131 \/ R_INT01
                                \/ R200 \/ R201 \/ R202 \/ R_INT02 \/ R300
                                \/ R301 \/ R302 \/ R303 \/ R304 \/ R305
                                \/ R306 \/ R307 \/ R308 \/ R309 \/ R310
                                \/ R311 \/ R312 \/ R313 \/ R314 \/ R_INT03
                                \/ R400

H000 == /\ pc = "H000"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] + 1]
        /\ pc' = "H001"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H001 == /\ pc = "H001"
        /\ registers' = [registers EXCEPT !["x1"] = registers["x1"] + 1]
        /\ pc' = "H002"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H002 == /\ pc = "H002"
        /\ registers' = [registers EXCEPT !["x2"] = registers["x2"] + 1]
        /\ pc' = "H003"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H003 == /\ pc = "H003"
        /\ registers' = [registers EXCEPT !["x3"] = registers["x3"] + 1]
        /\ pc' = "H004"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H004 == /\ pc = "H004"
        /\ registers' = [registers EXCEPT !["x4"] = registers["x4"] + 1]
        /\ pc' = "H005"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H005 == /\ pc = "H005"
        /\ registers' = [registers EXCEPT !["x5"] = registers["x5"] + 1]
        /\ pc' = "H006"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H006 == /\ pc = "H006"
        /\ registers' = [registers EXCEPT !["x6"] = registers["x6"] + 1]
        /\ pc' = "H007"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H007 == /\ pc = "H007"
        /\ registers' = [registers EXCEPT !["x7"] = registers["x7"] + 1]
        /\ pc' = "H008"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H008 == /\ pc = "H008"
        /\ registers' = [registers EXCEPT !["x8"] = registers["x8"] + 1]
        /\ pc' = "H009"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H009 == /\ pc = "H009"
        /\ registers' = [registers EXCEPT !["x9"] = registers["x9"] + 1]
        /\ pc' = "H010"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H010 == /\ pc = "H010"
        /\ registers' = [registers EXCEPT !["x10"] = registers["x10"] + 1]
        /\ pc' = "H011"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H011 == /\ pc = "H011"
        /\ registers' = [registers EXCEPT !["x11"] = registers["x11"] + 1]
        /\ pc' = "H012"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H012 == /\ pc = "H012"
        /\ registers' = [registers EXCEPT !["x12"] = registers["x12"] + 1]
        /\ pc' = "H013"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H013 == /\ pc = "H013"
        /\ registers' = [registers EXCEPT !["x13"] = registers["x13"] + 1]
        /\ pc' = "H014"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H014 == /\ pc = "H014"
        /\ registers' = [registers EXCEPT !["x14"] = registers["x14"] + 1]
        /\ pc' = "H015"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H015 == /\ pc = "H015"
        /\ registers' = [registers EXCEPT !["x15"] = registers["x15"] + 1]
        /\ pc' = "H016"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H016 == /\ pc = "H016"
        /\ registers' = [registers EXCEPT !["x16"] = registers["x16"] + 1]
        /\ pc' = "H017"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H017 == /\ pc = "H017"
        /\ registers' = [registers EXCEPT !["x17"] = registers["x17"] + 1]
        /\ pc' = "H018"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H018 == /\ pc = "H018"
        /\ registers' = [registers EXCEPT !["x18"] = registers["x18"] + 1]
        /\ pc' = "H019"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H019 == /\ pc = "H019"
        /\ registers' = [registers EXCEPT !["x19"] = registers["x19"] + 1]
        /\ pc' = "H020"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H020 == /\ pc = "H020"
        /\ registers' = [registers EXCEPT !["x20"] = registers["x20"] + 1]
        /\ pc' = "H021"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H021 == /\ pc = "H021"
        /\ registers' = [registers EXCEPT !["x21"] = registers["x21"] + 1]
        /\ pc' = "H022"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H022 == /\ pc = "H022"
        /\ registers' = [registers EXCEPT !["x22"] = registers["x22"] + 1]
        /\ pc' = "H023"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H023 == /\ pc = "H023"
        /\ registers' = [registers EXCEPT !["x23"] = registers["x23"] + 1]
        /\ pc' = "H024"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H024 == /\ pc = "H024"
        /\ registers' = [registers EXCEPT !["x24"] = registers["x24"] + 1]
        /\ pc' = "H025"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H025 == /\ pc = "H025"
        /\ registers' = [registers EXCEPT !["x25"] = registers["x25"] + 1]
        /\ pc' = "H026"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H026 == /\ pc = "H026"
        /\ registers' = [registers EXCEPT !["x26"] = registers["x26"] + 1]
        /\ pc' = "H027"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H027 == /\ pc = "H027"
        /\ registers' = [registers EXCEPT !["x27"] = registers["x27"] + 1]
        /\ pc' = "H028"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H028 == /\ pc = "H028"
        /\ registers' = [registers EXCEPT !["x28"] = registers["x28"] + 1]
        /\ pc' = "H029"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H029 == /\ pc = "H029"
        /\ registers' = [registers EXCEPT !["x29"] = registers["x29"] + 1]
        /\ pc' = "H030"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H030 == /\ pc = "H030"
        /\ registers' = [registers EXCEPT !["lr"] = registers["lr"] + 1]
        /\ pc' = "H_INT00"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H_INT00 == /\ pc = "H_INT00"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "H100" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

H100 == /\ pc = "H100"
        /\ registers' = [registers EXCEPT !["q0"] = registers["q0"] + 1]
        /\ pc' = "H101"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H101 == /\ pc = "H101"
        /\ registers' = [registers EXCEPT !["q1"] = registers["q1"] + 1]
        /\ pc' = "H102"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H102 == /\ pc = "H102"
        /\ registers' = [registers EXCEPT !["q2"] = registers["q2"] + 1]
        /\ pc' = "H103"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H103 == /\ pc = "H103"
        /\ registers' = [registers EXCEPT !["q3"] = registers["q3"] + 1]
        /\ pc' = "H104"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H104 == /\ pc = "H104"
        /\ registers' = [registers EXCEPT !["q4"] = registers["q4"] + 1]
        /\ pc' = "H105"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H105 == /\ pc = "H105"
        /\ registers' = [registers EXCEPT !["q5"] = registers["q5"] + 1]
        /\ pc' = "H106"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H106 == /\ pc = "H106"
        /\ registers' = [registers EXCEPT !["q6"] = registers["q6"] + 1]
        /\ pc' = "H107"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H107 == /\ pc = "H107"
        /\ registers' = [registers EXCEPT !["q7"] = registers["q7"] + 1]
        /\ pc' = "H108"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H108 == /\ pc = "H108"
        /\ registers' = [registers EXCEPT !["q8"] = registers["q8"] + 1]
        /\ pc' = "H109"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H109 == /\ pc = "H109"
        /\ registers' = [registers EXCEPT !["q9"] = registers["q9"] + 1]
        /\ pc' = "H110"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H110 == /\ pc = "H110"
        /\ registers' = [registers EXCEPT !["q10"] = registers["q10"] + 1]
        /\ pc' = "H111"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H111 == /\ pc = "H111"
        /\ registers' = [registers EXCEPT !["q11"] = registers["q11"] + 1]
        /\ pc' = "H112"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H112 == /\ pc = "H112"
        /\ registers' = [registers EXCEPT !["q12"] = registers["q12"] + 1]
        /\ pc' = "H113"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H113 == /\ pc = "H113"
        /\ registers' = [registers EXCEPT !["q13"] = registers["q13"] + 1]
        /\ pc' = "H114"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H114 == /\ pc = "H114"
        /\ registers' = [registers EXCEPT !["q14"] = registers["q14"] + 1]
        /\ pc' = "H115"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H115 == /\ pc = "H115"
        /\ registers' = [registers EXCEPT !["q15"] = registers["q15"] + 1]
        /\ pc' = "H116"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H116 == /\ pc = "H116"
        /\ registers' = [registers EXCEPT !["q16"] = registers["q16"] + 1]
        /\ pc' = "H117"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H117 == /\ pc = "H117"
        /\ registers' = [registers EXCEPT !["q17"] = registers["q17"] + 1]
        /\ pc' = "H118"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H118 == /\ pc = "H118"
        /\ registers' = [registers EXCEPT !["q18"] = registers["q18"] + 1]
        /\ pc' = "H119"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H119 == /\ pc = "H119"
        /\ registers' = [registers EXCEPT !["q19"] = registers["q19"] + 1]
        /\ pc' = "H120"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H120 == /\ pc = "H120"
        /\ registers' = [registers EXCEPT !["q20"] = registers["q20"] + 1]
        /\ pc' = "H121"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H121 == /\ pc = "H121"
        /\ registers' = [registers EXCEPT !["q21"] = registers["q21"] + 1]
        /\ pc' = "H122"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H122 == /\ pc = "H122"
        /\ registers' = [registers EXCEPT !["q22"] = registers["q22"] + 1]
        /\ pc' = "H123"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H123 == /\ pc = "H123"
        /\ registers' = [registers EXCEPT !["q23"] = registers["q23"] + 1]
        /\ pc' = "H124"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H124 == /\ pc = "H124"
        /\ registers' = [registers EXCEPT !["q24"] = registers["q24"] + 1]
        /\ pc' = "H125"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H125 == /\ pc = "H125"
        /\ registers' = [registers EXCEPT !["q25"] = registers["q25"] + 1]
        /\ pc' = "H126"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H126 == /\ pc = "H126"
        /\ registers' = [registers EXCEPT !["q26"] = registers["q26"] + 1]
        /\ pc' = "H127"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H127 == /\ pc = "H127"
        /\ registers' = [registers EXCEPT !["q27"] = registers["q27"] + 1]
        /\ pc' = "H128"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H128 == /\ pc = "H128"
        /\ registers' = [registers EXCEPT !["q28"] = registers["q28"] + 1]
        /\ pc' = "H129"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H129 == /\ pc = "H129"
        /\ registers' = [registers EXCEPT !["q29"] = registers["q29"] + 1]
        /\ pc' = "H130"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H130 == /\ pc = "H130"
        /\ registers' = [registers EXCEPT !["q30"] = registers["q30"] + 1]
        /\ pc' = "H131"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H131 == /\ pc = "H131"
        /\ registers' = [registers EXCEPT !["q31"] = registers["q31"] + 1]
        /\ pc' = "H_INT01"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H_INT01 == /\ pc = "H_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "H200" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                           offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                           offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                           offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                           addr, ctx_start >>

H200 == /\ pc = "H200"
        /\ registers' = [registers EXCEPT !["elr"] = registers["elr"] + 1]
        /\ pc' = "H201"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H201 == /\ pc = "H201"
        /\ registers' = [registers EXCEPT !["spsr"] = registers["spsr"] + 1]
        /\ pc' = "H202"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H202 == /\ pc = "H202"
        /\ registers' = [registers EXCEPT !["fpsr"] = registers["fpsr"] + 1]
        /\ pc' = "H203"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

H203 == /\ pc = "H203"
        /\ registers' = [registers EXCEPT !["fpcr"] = registers["fpcr"] + 1]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                        reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                        reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

handler == H000 \/ H001 \/ H002 \/ H003 \/ H004 \/ H005 \/ H006 \/ H007
              \/ H008 \/ H009 \/ H010 \/ H011 \/ H012 \/ H013 \/ H014
              \/ H015 \/ H016 \/ H017 \/ H018 \/ H019 \/ H020 \/ H021
              \/ H022 \/ H023 \/ H024 \/ H025 \/ H026 \/ H027 \/ H028
              \/ H029 \/ H030 \/ H_INT00 \/ H100 \/ H101 \/ H102 \/ H103
              \/ H104 \/ H105 \/ H106 \/ H107 \/ H108 \/ H109 \/ H110
              \/ H111 \/ H112 \/ H113 \/ H114 \/ H115 \/ H116 \/ H117
              \/ H118 \/ H119 \/ H120 \/ H121 \/ H122 \/ H123 \/ H124
              \/ H125 \/ H126 \/ H127 \/ H128 \/ H129 \/ H130 \/ H131
              \/ H_INT01 \/ H200 \/ H201 \/ H202 \/ H203

start == /\ pc = "start"
         /\ stack' = << [ procedure |->  "CALL_WITH_CONTEXT",
                          pc        |->  "Done",
                          ctx_start |->  ctx_start ] >>
                      \o stack
         /\ ctx_start' = defaultInitValue
         /\ pc' = "start_call_with_context"
         /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                         offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                         reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                         offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                         offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                         offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == interrupt \/ data_abort_exception \/ str \/ ldr \/ str_add
           \/ ldr_add \/ stp \/ ldp \/ ldp_add \/ CALL_WITH_CONTEXT
           \/ exception_store_registers \/ exception_restore_context \/ handler
           \/ start
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
