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
        x30 |-> 30, \* equivalent to "lr"

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
        registers[reg2] := registers[reg2] + offset;
        return;
end procedure;

\* str reg1, [reg2, offset]
\*
\* reg1 = [reg2];
\* reg2 = reg2 + offset;
procedure ldr_add(reg1, reg2, offset)
variables
    addr
begin
    ldr_add0:
        addr := registers[reg2];
        if addr < 0 \/ addr >= STACK_SIZE then
            call data_abort_exception();
        end if;
    ldr_add1:
        registers[reg1] := stack_memory[addr];
    ldr_add2:
        registers[reg2] := registers[reg2] + offset;
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

\* stp reg1, reg2, [reg3, offset]
\*
\* [reg3] = reg1;
\* [reg3 + 8] = reg2;
\* reg3 = reg3 + offset;
procedure stp_add(reg1, reg2, reg3, offset)
variables
    addr;
begin
    stp_add0:
        addr := registers[reg3];
        if addr < 0 \/ addr + 8 >= STACK_SIZE then
            call data_abort_exception();
        end if;
    stp_add1:
        stack_memory[addr] := registers[reg1];
    stp_add2:
        stack_memory[addr + 8] := registers[reg2];
        registers[reg3] := registers[reg3] + offset;
        return;
end procedure;

\* stp reg1, reg2, [reg3], offset
\*
\* [reg3 + offset] = reg1;
\* [reg3 + offset + 16] = reg2;
\* reg3 = reg3 + offset
procedure stp16_add(reg1, reg2, reg3, offset)
variables
    addr;
begin
    stp16_0:
        addr := registers[reg3];
        if addr < 0 \/ addr + 16 >= STACK_SIZE then
            call data_abort_exception();
        end if;
    stp16_1:
        stack_memory[addr] := registers[reg1];
    stp16_2:
        stack_memory[addr + 16] := registers[reg2];
    stp16_3:
        registers[reg3] := addr + offset;
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

\* ldp reg1, reg2, [reg3], offset
\*
\* reg1 = [reg3];
\* reg2 = [reg3 + 16];
\* reg3 = reg3 + offset;
procedure ldp16_add(reg1, reg2, reg3, offset)
variables
    addr;
begin
    ldp_add0:
        addr := registers[reg3];
        if addr < 0 \/ addr + 16 >= STACK_SIZE then
            call data_abort_exception();
        end if;
    ldp_add1:
        registers[reg1] := stack_memory[addr];
    ldp_add2:
        registers[reg2] := stack_memory[addr + 16];
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

    \* disable interrupt
    \* msr     DAIFSet, #0x02

    \* Make room on the stack for the exception context.
    C000: sub("sp", "sp", 800);

    C_INT00: call interrupt();

    \* Store x0 - x3, x30, and ELR on the stack.
    C001: call stp("x0", "x1", "sp", 0);

    C002: mrs("x1", "elr");

    C003: call stp("x2", "x3", "sp", 16);
    C004: call stp("x30", "x1", "sp", 240);

    C005: add("x0", "sp", 32);
    C006: mrs("x2", "esr");
    C007: mrs("x3", "spsr");

    C_INT01: call interrupt();

    C100: call exception_store_registers();

    C_INT02: call interrupt();

    \* x0 is the first argument of `\handler`.
    C101: mov("x0", "sp"); \* Context

    \* x1 is the second argument fo `\handler`.
    C102: add("x1", "sp", 800);

    \* Call `\handler`.
    C103: call handler();

    C_INT03: call interrupt();

    C200: add("x0", "sp", 248);

    C201: call ldp_add("x1", "x2", "x0", 16); \* ELR and ESR

    C202: call ldr_add("x3", "x0", 8); \* SPSR

    C203: msr("elr", "x1"); \* Restore ELR.
    C204: msr("esr", "x2"); \* Restore ESR.
    C205: msr("spsr", "x3"); \* Restore SPSR.

    C206: call exception_restore_context();

    end_call_with_context:
        assert ctx_start = registers;
        return;
end procedure;

procedure exception_store_registers() begin
    \* Store general purpose registers.
    S000: call stp_add( "x4",  "x5", "x0", 16);
    S001: call stp_add( "x6",  "x7", "x0", 16);
    S002: call stp_add( "x8",  "x9", "x0", 16);
    S003: call stp_add("x10", "x11", "x0", 16);
    S004: call stp_add("x12", "x13", "x0", 16);
    S005: call stp_add("x14", "x15", "x0", 16);
    S006: call stp_add("x16", "x17", "x0", 16);
    S007: call stp_add("x18", "x19", "x0", 16);
    S008: call stp_add("x20", "x21", "x0", 16);
    S009: call stp_add("x22", "x23", "x0", 16);
    S010: call stp_add("x24", "x25", "x0", 16);
    S011: call stp_add("x26", "x27", "x0", 16);
    S012: call stp_add("x28", "x29", "x0", 32);

    \* Store ESR and SPSR.
    S100: call str_add("x2", "x0", 8);
    S101: call str_add("x3", "x0", 8);

    \* Store FPSR and FPCR.
    S102: mrs("x4", "fpsr");
    S104: mrs("x5", "fpcr");
    S103: call stp_add("x4", "x5", "x0", 16);

    S_INT01: call interrupt();

    \* Store all floating-point registers.
    S200: call stp16_add( "q0",  "q1", "x0", 32);
    S201: call stp16_add( "q2",  "q3", "x0", 32);
    S202: call stp16_add( "q4",  "q5", "x0", 32);
    S203: call stp16_add( "q6",  "q7", "x0", 32);
    S204: call stp16_add( "q8",  "q9", "x0", 32);
    S205: call stp16_add("q10", "q11", "x0", 32);
    S206: call stp16_add("q12", "q13", "x0", 32);
    S207: call stp16_add("q14", "q15", "x0", 32);
    S208: call stp16_add("q16", "q17", "x0", 32);
    S209: call stp16_add("q18", "q19", "x0", 32);
    S210: call stp16_add("q20", "q21", "x0", 32);
    S211: call stp16_add("q22", "q23", "x0", 32);
    S212: call stp16_add("q24", "q25", "x0", 32);
    S213: call stp16_add("q26", "q27", "x0", 32);
    S214: call stp16_add("q28", "q29", "x0", 32);
    S215: call stp16_add("q30", "q31", "x0", 32);

    return;
end procedure;

procedure exception_restore_context() begin
    R000: call ldp_add("x1", "x2", "x0", 16); \* Load FPSR and FPCR.

    R001: msr("fpsr", "x1");
    R002: msr("fpcr", "x2");

    R100: call ldp16_add( "q0",  "q1", "x0", 32);
    R101: call ldp16_add( "q2",  "q3", "x0", 32);
    R102: call ldp16_add( "q4",  "q5", "x0", 32);
    R103: call ldp16_add( "q6",  "q7", "x0", 32);
    R104: call ldp16_add( "q8",  "q9", "x0", 32);
    R105: call ldp16_add("q10", "q11", "x0", 32);
    R106: call ldp16_add("q12", "q13", "x0", 32);
    R107: call ldp16_add("q14", "q15", "x0", 32);
    R108: call ldp16_add("q16", "q17", "x0", 32);
    R109: call ldp16_add("q18", "q19", "x0", 32);
    R110: call ldp16_add("q20", "q21", "x0", 32);
    R111: call ldp16_add("q22", "q23", "x0", 32);
    R112: call ldp16_add("q24", "q25", "x0", 32);
    R113: call ldp16_add("q26", "q27", "x0", 32);
    R114: call ldp16_add("q28", "q29", "x0", 32);
    R115: call ldp16_add("q30", "q31", "x0", 0);

    R200: mov("x30", "sp");

    R_INT01: call interrupt();

    R300: call ldp_add( "x0",  "x1", "x30", 16);
    R301: call ldp_add( "x2",  "x3", "x30", 16);
    R302: call ldp_add( "x4",  "x5", "x30", 16);
    R303: call ldp_add( "x6",  "x7", "x30", 16);
    R304: call ldp_add( "x8",  "x9", "x30", 16);
    R305: call ldp_add("x10", "x11", "x30", 16);
    R306: call ldp_add("x12", "x13", "x30", 16);
    R307: call ldp_add("x14", "x15", "x30", 16);
    R308: call ldp_add("x16", "x17", "x30", 16);
    R309: call ldp_add("x18", "x19", "x30", 16);
    R310: call ldp_add("x20", "x21", "x30", 16);
    R311: call ldp_add("x22", "x23", "x30", 16);
    R312: call ldp_add("x24", "x25", "x30", 16);
    R313: call ldp_add("x26", "x27", "x30", 16);
    R314: call ldp_add("x28", "x29", "x30", 16);
    R315: call ldr_add("x30", "x30", 0);

    R_INT02: call interrupt();

    R400: add("sp", "sp", 800); \* Restore SP.

    \* enable interrupt
    \* msr     DAIFClr, #0x02

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
    H030: inc("x30");

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

\* BEGIN TRANSLATION (chksum(pcal) = "7c93441d" /\ chksum(tla) = "65634d8e")
\* Label ldp_add0 of procedure ldp_add at line 261 col 9 changed to ldp_add0_
\* Label ldp_add1 of procedure ldp_add at line 266 col 9 changed to ldp_add1_
\* Label ldp_add2 of procedure ldp_add at line 268 col 9 changed to ldp_add2_
\* Label ldp_add3 of procedure ldp_add at line 270 col 9 changed to ldp_add3_
\* Procedure variable addr of procedure str_add at line 153 col 5 changed to addr_
\* Procedure variable addr of procedure ldr_add at line 172 col 5 changed to addr_l
\* Procedure variable addr of procedure stp at line 192 col 5 changed to addr_s
\* Procedure variable addr of procedure stp_add at line 213 col 5 changed to addr_st
\* Procedure variable addr of procedure stp16_add at line 235 col 5 changed to addr_stp
\* Procedure variable addr of procedure ldp_add at line 258 col 5 changed to addr_ld
\* Parameter reg1 of procedure str_add at line 151 col 19 changed to reg1_
\* Parameter reg2 of procedure str_add at line 151 col 25 changed to reg2_
\* Parameter offset of procedure str_add at line 151 col 31 changed to offset_
\* Parameter reg1 of procedure ldr_add at line 170 col 19 changed to reg1_l
\* Parameter reg2 of procedure ldr_add at line 170 col 25 changed to reg2_l
\* Parameter offset of procedure ldr_add at line 170 col 31 changed to offset_l
\* Parameter reg1 of procedure stp at line 190 col 15 changed to reg1_s
\* Parameter reg2 of procedure stp at line 190 col 21 changed to reg2_s
\* Parameter reg3 of procedure stp at line 190 col 27 changed to reg3_
\* Parameter offset of procedure stp at line 190 col 33 changed to offset_s
\* Parameter reg1 of procedure stp_add at line 211 col 19 changed to reg1_st
\* Parameter reg2 of procedure stp_add at line 211 col 25 changed to reg2_st
\* Parameter reg3 of procedure stp_add at line 211 col 31 changed to reg3_s
\* Parameter offset of procedure stp_add at line 211 col 37 changed to offset_st
\* Parameter reg1 of procedure stp16_add at line 233 col 21 changed to reg1_stp
\* Parameter reg2 of procedure stp16_add at line 233 col 27 changed to reg2_stp
\* Parameter reg3 of procedure stp16_add at line 233 col 33 changed to reg3_st
\* Parameter offset of procedure stp16_add at line 233 col 39 changed to offset_stp
\* Parameter reg1 of procedure ldp_add at line 256 col 19 changed to reg1_ld
\* Parameter reg2 of procedure ldp_add at line 256 col 25 changed to reg2_ld
\* Parameter reg3 of procedure ldp_add at line 256 col 31 changed to reg3_l
\* Parameter offset of procedure ldp_add at line 256 col 37 changed to offset_ld
CONSTANT defaultInitValue
VARIABLES data_abort, stack_memory, registers, pc, stack, reg1_, reg2_, 
          offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
          reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
          addr_st, reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
          reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
          ctx_start

vars == << data_abort, stack_memory, registers, pc, stack, reg1_, reg2_, 
           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
           reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
           addr_st, reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, 
           reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
           offset, addr, ctx_start >>

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
                           x30 |-> 30,
                       
                       
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
        (* Procedure str_add *)
        /\ reg1_ = defaultInitValue
        /\ reg2_ = defaultInitValue
        /\ offset_ = defaultInitValue
        /\ addr_ = defaultInitValue
        (* Procedure ldr_add *)
        /\ reg1_l = defaultInitValue
        /\ reg2_l = defaultInitValue
        /\ offset_l = defaultInitValue
        /\ addr_l = defaultInitValue
        (* Procedure stp *)
        /\ reg1_s = defaultInitValue
        /\ reg2_s = defaultInitValue
        /\ reg3_ = defaultInitValue
        /\ offset_s = defaultInitValue
        /\ addr_s = defaultInitValue
        (* Procedure stp_add *)
        /\ reg1_st = defaultInitValue
        /\ reg2_st = defaultInitValue
        /\ reg3_s = defaultInitValue
        /\ offset_st = defaultInitValue
        /\ addr_st = defaultInitValue
        (* Procedure stp16_add *)
        /\ reg1_stp = defaultInitValue
        /\ reg2_stp = defaultInitValue
        /\ reg3_st = defaultInitValue
        /\ offset_stp = defaultInitValue
        /\ addr_stp = defaultInitValue
        (* Procedure ldp_add *)
        /\ reg1_ld = defaultInitValue
        /\ reg2_ld = defaultInitValue
        /\ reg3_l = defaultInitValue
        /\ offset_ld = defaultInitValue
        /\ addr_ld = defaultInitValue
        (* Procedure ldp16_add *)
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
                                   offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                                   offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                                   offset_st, addr_st, reg1_stp, reg2_stp, 
                                   reg3_st, offset_stp, addr_stp, reg1_ld, 
                                   reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                                   reg2, reg3, offset, addr >>

end_interrupt == /\ pc = "end_interrupt"
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, 
                                 reg2_, offset_, addr_, reg1_l, reg2_l, 
                                 offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                                 offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                                 offset_st, addr_st, reg1_stp, reg2_stp, 
                                 reg3_st, offset_stp, addr_stp, reg1_ld, 
                                 reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                                 reg2, reg3, offset, addr, ctx_start >>

interrupt == start_interrupt \/ end_interrupt

loop_data_abort == /\ pc = "loop_data_abort"
                   /\ data_abort' = TRUE
                   /\ pc' = "loop_data_abort"
                   /\ UNCHANGED << stack_memory, registers, stack, reg1_, 
                                   reg2_, offset_, addr_, reg1_l, reg2_l, 
                                   offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                                   offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                                   offset_st, addr_st, reg1_stp, reg2_stp, 
                                   reg3_st, offset_stp, addr_stp, reg1_ld, 
                                   reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                                   reg2, reg3, offset, addr, ctx_start >>

data_abort_exception == loop_data_abort

str_add0 == /\ pc = "str_add0"
            /\ addr_' = registers[reg2_]
            /\ IF addr_' < 0 \/ addr_' >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "str_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "str_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                            reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                            reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                            reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                            offset, addr, ctx_start >>

str_add1 == /\ pc = "str_add1"
            /\ stack_memory' = [stack_memory EXCEPT ![addr_] = registers[reg1_]]
            /\ registers' = [registers EXCEPT ![reg2_] = registers[reg2_] + offset_]
            /\ pc' = Head(stack).pc
            /\ addr_' = Head(stack).addr_
            /\ reg1_' = Head(stack).reg1_
            /\ reg2_' = Head(stack).reg2_
            /\ offset_' = Head(stack).offset_
            /\ stack' = Tail(stack)
            /\ UNCHANGED << data_abort, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                            reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                            reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                            reg3, offset, addr, ctx_start >>

str_add == str_add0 \/ str_add1

ldr_add0 == /\ pc = "ldr_add0"
            /\ addr_l' = registers[reg2_l]
            /\ IF addr_l' < 0 \/ addr_l' >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "ldr_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "ldr_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, reg1_s, 
                            reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                            reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                            reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                            reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                            offset, addr, ctx_start >>

ldr_add1 == /\ pc = "ldr_add1"
            /\ registers' = [registers EXCEPT ![reg1_l] = stack_memory[addr_l]]
            /\ pc' = "ldr_add2"
            /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                            reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                            reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                            reg3, offset, addr, ctx_start >>

ldr_add2 == /\ pc = "ldr_add2"
            /\ registers' = [registers EXCEPT ![reg2_l] = registers[reg2_l] + offset_l]
            /\ pc' = Head(stack).pc
            /\ addr_l' = Head(stack).addr_l
            /\ reg1_l' = Head(stack).reg1_l
            /\ reg2_l' = Head(stack).reg2_l
            /\ offset_l' = Head(stack).offset_l
            /\ stack' = Tail(stack)
            /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, 
                            addr_, reg1_s, reg2_s, reg3_, offset_s, addr_s, 
                            reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                            reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, 
                            reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                            reg2, reg3, offset, addr, ctx_start >>

ldr_add == ldr_add0 \/ ldr_add1 \/ ldr_add2

stp0 == /\ pc = "stp0"
        /\ addr_s' = registers[reg3_] + offset_s
        /\ IF addr_s' < 0 \/ addr_s' + 8 >= STACK_SIZE
              THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                    pc        |->  "stp1" ] >>
                                \o stack
                   /\ pc' = "loop_data_abort"
              ELSE /\ pc' = "stp1"
                   /\ stack' = stack
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

stp1 == /\ pc = "stp1"
        /\ stack_memory' = [stack_memory EXCEPT ![addr_s] = registers[reg1_s]]
        /\ pc' = "stp2"
        /\ UNCHANGED << data_abort, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

stp2 == /\ pc = "stp2"
        /\ stack_memory' = [stack_memory EXCEPT ![addr_s + 8] = registers[reg2_s]]
        /\ pc' = Head(stack).pc
        /\ addr_s' = Head(stack).addr_s
        /\ reg1_s' = Head(stack).reg1_s
        /\ reg2_s' = Head(stack).reg2_s
        /\ reg3_' = Head(stack).reg3_
        /\ offset_s' = Head(stack).offset_s
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

stp == stp0 \/ stp1 \/ stp2

stp_add0 == /\ pc = "stp_add0"
            /\ addr_st' = registers[reg3_s]
            /\ IF addr_st' < 0 \/ addr_st' + 8 >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "stp_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "stp_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, reg1_stp, reg2_stp, 
                            reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                            reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                            offset, addr, ctx_start >>

stp_add1 == /\ pc = "stp_add1"
            /\ stack_memory' = [stack_memory EXCEPT ![addr_st] = registers[reg1_st]]
            /\ pc' = "stp_add2"
            /\ UNCHANGED << data_abort, registers, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                            reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                            reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                            reg3, offset, addr, ctx_start >>

stp_add2 == /\ pc = "stp_add2"
            /\ stack_memory' = [stack_memory EXCEPT ![addr_st + 8] = registers[reg2_st]]
            /\ registers' = [registers EXCEPT ![reg3_s] = registers[reg3_s] + offset_st]
            /\ pc' = Head(stack).pc
            /\ addr_st' = Head(stack).addr_st
            /\ reg1_st' = Head(stack).reg1_st
            /\ reg2_st' = Head(stack).reg2_st
            /\ reg3_s' = Head(stack).reg3_s
            /\ offset_st' = Head(stack).offset_st
            /\ stack' = Tail(stack)
            /\ UNCHANGED << data_abort, reg1_, reg2_, offset_, addr_, reg1_l, 
                            reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                            offset_s, addr_s, reg1_stp, reg2_stp, reg3_st, 
                            offset_stp, addr_stp, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            ctx_start >>

stp_add == stp_add0 \/ stp_add1 \/ stp_add2

stp16_0 == /\ pc = "stp16_0"
           /\ addr_stp' = registers[reg3_st]
           /\ IF addr_stp' < 0 \/ addr_stp' + 16 >= STACK_SIZE
                 THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                       pc        |->  "stp16_1" ] >>
                                   \o stack
                      /\ pc' = "loop_data_abort"
                 ELSE /\ pc' = "stp16_1"
                      /\ stack' = stack
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, reg1_ld, reg2_ld, 
                           reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                           offset, addr, ctx_start >>

stp16_1 == /\ pc = "stp16_1"
           /\ stack_memory' = [stack_memory EXCEPT ![addr_stp] = registers[reg1_stp]]
           /\ pc' = "stp16_2"
           /\ UNCHANGED << data_abort, registers, stack, reg1_, reg2_, offset_, 
                           addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                           reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                           reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                           reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                           reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                           offset, addr, ctx_start >>

stp16_2 == /\ pc = "stp16_2"
           /\ stack_memory' = [stack_memory EXCEPT ![addr_stp + 16] = registers[reg2_stp]]
           /\ pc' = "stp16_3"
           /\ UNCHANGED << data_abort, registers, stack, reg1_, reg2_, offset_, 
                           addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                           reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                           reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                           reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                           reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                           offset, addr, ctx_start >>

stp16_3 == /\ pc = "stp16_3"
           /\ registers' = [registers EXCEPT ![reg3_st] = addr_stp + offset_stp]
           /\ pc' = Head(stack).pc
           /\ addr_stp' = Head(stack).addr_stp
           /\ reg1_stp' = Head(stack).reg1_stp
           /\ reg2_stp' = Head(stack).reg2_stp
           /\ reg3_st' = Head(stack).reg3_st
           /\ offset_stp' = Head(stack).offset_stp
           /\ stack' = Tail(stack)
           /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, 
                           addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                           reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                           reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                           reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                           offset, addr, ctx_start >>

stp16_add == stp16_0 \/ stp16_1 \/ stp16_2 \/ stp16_3

ldp_add0_ == /\ pc = "ldp_add0_"
             /\ addr_ld' = registers[reg3_l]
             /\ IF addr_ld' < 0 \/ addr_ld' + 8 >= STACK_SIZE
                   THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                         pc        |->  "ldp_add1_" ] >>
                                     \o stack
                        /\ pc' = "loop_data_abort"
                   ELSE /\ pc' = "ldp_add1_"
                        /\ stack' = stack
             /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                             offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                             reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                             reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                             reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                             reg2_ld, reg3_l, offset_ld, reg1, reg2, reg3, 
                             offset, addr, ctx_start >>

ldp_add1_ == /\ pc = "ldp_add1_"
             /\ registers' = [registers EXCEPT ![reg1_ld] = stack_memory[addr_ld]]
             /\ pc' = "ldp_add2_"
             /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                             offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                             reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                             reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                             reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                             reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                             reg3, offset, addr, ctx_start >>

ldp_add2_ == /\ pc = "ldp_add2_"
             /\ registers' = [registers EXCEPT ![reg2_ld] = stack_memory[addr_ld + 8]]
             /\ pc' = "ldp_add3_"
             /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                             offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                             reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                             reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                             reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                             reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                             reg3, offset, addr, ctx_start >>

ldp_add3_ == /\ pc = "ldp_add3_"
             /\ registers' = [registers EXCEPT ![reg3_l] = addr_ld + offset_ld]
             /\ pc' = Head(stack).pc
             /\ addr_ld' = Head(stack).addr_ld
             /\ reg1_ld' = Head(stack).reg1_ld
             /\ reg2_ld' = Head(stack).reg2_ld
             /\ reg3_l' = Head(stack).reg3_l
             /\ offset_ld' = Head(stack).offset_ld
             /\ stack' = Tail(stack)
             /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, 
                             addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                             reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                             reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                             reg3_st, offset_stp, addr_stp, reg1, reg2, reg3, 
                             offset, addr, ctx_start >>

ldp_add == ldp_add0_ \/ ldp_add1_ \/ ldp_add2_ \/ ldp_add3_

ldp_add0 == /\ pc = "ldp_add0"
            /\ addr' = registers[reg3]
            /\ IF addr' < 0 \/ addr' + 16 >= STACK_SIZE
                  THEN /\ stack' = << [ procedure |->  "data_abort_exception",
                                        pc        |->  "ldp_add1" ] >>
                                    \o stack
                       /\ pc' = "loop_data_abort"
                  ELSE /\ pc' = "ldp_add1"
                       /\ stack' = stack
            /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                            reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                            reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                            reg3, offset, ctx_start >>

ldp_add1 == /\ pc = "ldp_add1"
            /\ registers' = [registers EXCEPT ![reg1] = stack_memory[addr]]
            /\ pc' = "ldp_add2"
            /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                            reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                            reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                            reg3, offset, addr, ctx_start >>

ldp_add2 == /\ pc = "ldp_add2"
            /\ registers' = [registers EXCEPT ![reg2] = stack_memory[addr + 16]]
            /\ pc' = "ldp_add3"
            /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                            reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                            reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                            reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                            reg3, offset, addr, ctx_start >>

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
                            reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                            reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                            reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                            reg3_l, offset_ld, addr_ld, ctx_start >>

ldp16_add == ldp_add0 \/ ldp_add1 \/ ldp_add2 \/ ldp_add3

start_call_with_context == /\ pc = "start_call_with_context"
                           /\ ctx_start' = registers
                           /\ pc' = "C000"
                           /\ UNCHANGED << data_abort, stack_memory, registers, 
                                           stack, reg1_, reg2_, offset_, addr_, 
                                           reg1_l, reg2_l, offset_l, addr_l, 
                                           reg1_s, reg2_s, reg3_, offset_s, 
                                           addr_s, reg1_st, reg2_st, reg3_s, 
                                           offset_st, addr_st, reg1_stp, 
                                           reg2_stp, reg3_st, offset_stp, 
                                           addr_stp, reg1_ld, reg2_ld, reg3_l, 
                                           offset_ld, addr_ld, reg1, reg2, 
                                           reg3, offset, addr >>

C000 == /\ pc = "C000"
        /\ registers' = [registers EXCEPT !["sp"] = registers["sp"] - 800]
        /\ pc' = "C_INT00"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C_INT00 == /\ pc = "C_INT00"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C001" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

C001 == /\ pc = "C001"
        /\ /\ offset_s' = 0
           /\ reg1_s' = "x0"
           /\ reg2_s' = "x1"
           /\ reg3_' = "sp"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "C002",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_st, reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

C002 == /\ pc = "C002"
        /\ registers' = [registers EXCEPT !["x1"] = registers["elr"]]
        /\ pc' = "C003"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C003 == /\ pc = "C003"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x2"
           /\ reg2_s' = "x3"
           /\ reg3_' = "sp"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "C004",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_st, reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

C004 == /\ pc = "C004"
        /\ /\ offset_s' = 240
           /\ reg1_s' = "x30"
           /\ reg2_s' = "x1"
           /\ reg3_' = "sp"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "C005",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_st, reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

C005 == /\ pc = "C005"
        /\ registers' = [registers EXCEPT !["x0"] = registers["sp"] + 32]
        /\ pc' = "C006"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C006 == /\ pc = "C006"
        /\ registers' = [registers EXCEPT !["x2"] = registers["esr"]]
        /\ pc' = "C007"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C007 == /\ pc = "C007"
        /\ registers' = [registers EXCEPT !["x3"] = registers["spsr"]]
        /\ pc' = "C_INT01"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C_INT01 == /\ pc = "C_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C100" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

C100 == /\ pc = "C100"
        /\ stack' = << [ procedure |->  "exception_store_registers",
                         pc        |->  "C_INT02" ] >>
                     \o stack
        /\ pc' = "S000"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

C_INT02 == /\ pc = "C_INT02"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C101" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

C101 == /\ pc = "C101"
        /\ registers' = [registers EXCEPT !["x0"] = registers["sp"]]
        /\ pc' = "C102"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C102 == /\ pc = "C102"
        /\ registers' = [registers EXCEPT !["x1"] = registers["sp"] + 800]
        /\ pc' = "C103"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C103 == /\ pc = "C103"
        /\ stack' = << [ procedure |->  "handler",
                         pc        |->  "C_INT03" ] >>
                     \o stack
        /\ pc' = "H000"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

C_INT03 == /\ pc = "C_INT03"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "C200" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

C200 == /\ pc = "C200"
        /\ registers' = [registers EXCEPT !["x0"] = registers["sp"] + 248]
        /\ pc' = "C201"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C201 == /\ pc = "C201"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x1"
           /\ reg2_ld' = "x2"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "C202",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

C202 == /\ pc = "C202"
        /\ /\ offset_l' = 8
           /\ reg1_l' = "x3"
           /\ reg2_l' = "x0"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "C203",
                            addr_l    |->  addr_l,
                            reg1_l    |->  reg1_l,
                            reg2_l    |->  reg2_l,
                            offset_l  |->  offset_l ] >>
                        \o stack
        /\ addr_l' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                        reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, 
                        reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

C203 == /\ pc = "C203"
        /\ registers' = [registers EXCEPT !["elr"] = registers["x1"]]
        /\ pc' = "C204"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C204 == /\ pc = "C204"
        /\ registers' = [registers EXCEPT !["esr"] = registers["x2"]]
        /\ pc' = "C205"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C205 == /\ pc = "C205"
        /\ registers' = [registers EXCEPT !["spsr"] = registers["x3"]]
        /\ pc' = "C206"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

C206 == /\ pc = "C206"
        /\ stack' = << [ procedure |->  "exception_restore_context",
                         pc        |->  "end_call_with_context" ] >>
                     \o stack
        /\ pc' = "R000"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

end_call_with_context == /\ pc = "end_call_with_context"
                         /\ Assert(ctx_start = registers, 
                                   "Failure of assertion at line 354, column 9.")
                         /\ pc' = Head(stack).pc
                         /\ ctx_start' = Head(stack).ctx_start
                         /\ stack' = Tail(stack)
                         /\ UNCHANGED << data_abort, stack_memory, registers, 
                                         reg1_, reg2_, offset_, addr_, reg1_l, 
                                         reg2_l, offset_l, addr_l, reg1_s, 
                                         reg2_s, reg3_, offset_s, addr_s, 
                                         reg1_st, reg2_st, reg3_s, offset_st, 
                                         addr_st, reg1_stp, reg2_stp, reg3_st, 
                                         offset_stp, addr_stp, reg1_ld, 
                                         reg2_ld, reg3_l, offset_ld, addr_ld, 
                                         reg1, reg2, reg3, offset, addr >>

CALL_WITH_CONTEXT == start_call_with_context \/ C000 \/ C_INT00 \/ C001
                        \/ C002 \/ C003 \/ C004 \/ C005 \/ C006 \/ C007
                        \/ C_INT01 \/ C100 \/ C_INT02 \/ C101 \/ C102
                        \/ C103 \/ C_INT03 \/ C200 \/ C201 \/ C202 \/ C203
                        \/ C204 \/ C205 \/ C206 \/ end_call_with_context

S000 == /\ pc = "S000"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x4"
           /\ reg2_st' = "x5"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S001",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S001 == /\ pc = "S001"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x6"
           /\ reg2_st' = "x7"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S002",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S002 == /\ pc = "S002"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x8"
           /\ reg2_st' = "x9"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S003",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S003 == /\ pc = "S003"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x10"
           /\ reg2_st' = "x11"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S004",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S004 == /\ pc = "S004"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x12"
           /\ reg2_st' = "x13"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S005",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S005 == /\ pc = "S005"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x14"
           /\ reg2_st' = "x15"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S006",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S006 == /\ pc = "S006"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x16"
           /\ reg2_st' = "x17"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S007",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S007 == /\ pc = "S007"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x18"
           /\ reg2_st' = "x19"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S008",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S008 == /\ pc = "S008"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x20"
           /\ reg2_st' = "x21"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S009",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S009 == /\ pc = "S009"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x22"
           /\ reg2_st' = "x23"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S010",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S010 == /\ pc = "S010"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x24"
           /\ reg2_st' = "x25"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S011",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S011 == /\ pc = "S011"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x26"
           /\ reg2_st' = "x27"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S012",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S012 == /\ pc = "S012"
        /\ /\ offset_st' = 32
           /\ reg1_st' = "x28"
           /\ reg2_st' = "x29"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S100",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S100 == /\ pc = "S100"
        /\ /\ offset_' = 8
           /\ reg1_' = "x2"
           /\ reg2_' = "x0"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S101",
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                        reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, 
                        reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

S101 == /\ pc = "S101"
        /\ /\ offset_' = 8
           /\ reg1_' = "x3"
           /\ reg2_' = "x0"
           /\ stack' = << [ procedure |->  "str_add",
                            pc        |->  "S102",
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "str_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                        reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, 
                        reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

S102 == /\ pc = "S102"
        /\ registers' = [registers EXCEPT !["x4"] = registers["fpsr"]]
        /\ pc' = "S104"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S104 == /\ pc = "S104"
        /\ registers' = [registers EXCEPT !["x5"] = registers["fpcr"]]
        /\ pc' = "S103"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S103 == /\ pc = "S103"
        /\ /\ offset_st' = 16
           /\ reg1_st' = "x4"
           /\ reg2_st' = "x5"
           /\ reg3_s' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S_INT01",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_s    |->  reg3_s,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                        offset, addr, ctx_start >>

S_INT01 == /\ pc = "S_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "S200" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

S200 == /\ pc = "S200"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q0"
           /\ reg2_stp' = "q1"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S201",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S201 == /\ pc = "S201"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q2"
           /\ reg2_stp' = "q3"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S202",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S202 == /\ pc = "S202"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q4"
           /\ reg2_stp' = "q5"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S203",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S203 == /\ pc = "S203"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q6"
           /\ reg2_stp' = "q7"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S204",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S204 == /\ pc = "S204"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q8"
           /\ reg2_stp' = "q9"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S205",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S205 == /\ pc = "S205"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q10"
           /\ reg2_stp' = "q11"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S206",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S206 == /\ pc = "S206"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q12"
           /\ reg2_stp' = "q13"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S207",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S207 == /\ pc = "S207"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q14"
           /\ reg2_stp' = "q15"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S208",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S208 == /\ pc = "S208"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q16"
           /\ reg2_stp' = "q17"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S209",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S209 == /\ pc = "S209"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q18"
           /\ reg2_stp' = "q19"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S210",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S210 == /\ pc = "S210"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q20"
           /\ reg2_stp' = "q21"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S211",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S211 == /\ pc = "S211"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q22"
           /\ reg2_stp' = "q23"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S212",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S212 == /\ pc = "S212"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q24"
           /\ reg2_stp' = "q25"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S213",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S213 == /\ pc = "S213"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q26"
           /\ reg2_stp' = "q27"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S214",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S214 == /\ pc = "S214"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q28"
           /\ reg2_stp' = "q29"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  "S215",
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o stack
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

S215 == /\ pc = "S215"
        /\ /\ offset_stp' = 32
           /\ reg1_stp' = "q30"
           /\ reg2_stp' = "q31"
           /\ reg3_st' = "x0"
           /\ stack' = << [ procedure |->  "stp16_add",
                            pc        |->  Head(stack).pc,
                            addr_stp  |->  addr_stp,
                            reg1_stp  |->  reg1_stp,
                            reg2_stp  |->  reg2_stp,
                            reg3_st   |->  reg3_st,
                            offset_stp |->  offset_stp ] >>
                        \o Tail(stack)
        /\ addr_stp' = defaultInitValue
        /\ pc' = "stp16_0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

exception_store_registers == S000 \/ S001 \/ S002 \/ S003 \/ S004 \/ S005
                                \/ S006 \/ S007 \/ S008 \/ S009 \/ S010
                                \/ S011 \/ S012 \/ S100 \/ S101 \/ S102
                                \/ S104 \/ S103 \/ S_INT01 \/ S200 \/ S201
                                \/ S202 \/ S203 \/ S204 \/ S205 \/ S206
                                \/ S207 \/ S208 \/ S209 \/ S210 \/ S211
                                \/ S212 \/ S213 \/ S214 \/ S215

R000 == /\ pc = "R000"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x1"
           /\ reg2_ld' = "x2"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R001",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R001 == /\ pc = "R001"
        /\ registers' = [registers EXCEPT !["fpsr"] = registers["x1"]]
        /\ pc' = "R002"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

R002 == /\ pc = "R002"
        /\ registers' = [registers EXCEPT !["fpcr"] = registers["x2"]]
        /\ pc' = "R100"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

R100 == /\ pc = "R100"
        /\ /\ offset' = 32
           /\ reg1' = "q0"
           /\ reg2' = "q1"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R101",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R101 == /\ pc = "R101"
        /\ /\ offset' = 32
           /\ reg1' = "q2"
           /\ reg2' = "q3"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R102",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R102 == /\ pc = "R102"
        /\ /\ offset' = 32
           /\ reg1' = "q4"
           /\ reg2' = "q5"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R103",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R103 == /\ pc = "R103"
        /\ /\ offset' = 32
           /\ reg1' = "q6"
           /\ reg2' = "q7"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R104",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R104 == /\ pc = "R104"
        /\ /\ offset' = 32
           /\ reg1' = "q8"
           /\ reg2' = "q9"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R105",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R105 == /\ pc = "R105"
        /\ /\ offset' = 32
           /\ reg1' = "q10"
           /\ reg2' = "q11"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R106",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R106 == /\ pc = "R106"
        /\ /\ offset' = 32
           /\ reg1' = "q12"
           /\ reg2' = "q13"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R107",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R107 == /\ pc = "R107"
        /\ /\ offset' = 32
           /\ reg1' = "q14"
           /\ reg2' = "q15"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R108",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R108 == /\ pc = "R108"
        /\ /\ offset' = 32
           /\ reg1' = "q16"
           /\ reg2' = "q17"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R109",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R109 == /\ pc = "R109"
        /\ /\ offset' = 32
           /\ reg1' = "q18"
           /\ reg2' = "q19"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R110",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R110 == /\ pc = "R110"
        /\ /\ offset' = 32
           /\ reg1' = "q20"
           /\ reg2' = "q21"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R111",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R111 == /\ pc = "R111"
        /\ /\ offset' = 32
           /\ reg1' = "q22"
           /\ reg2' = "q23"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R112",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R112 == /\ pc = "R112"
        /\ /\ offset' = 32
           /\ reg1' = "q24"
           /\ reg2' = "q25"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R113",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R113 == /\ pc = "R113"
        /\ /\ offset' = 32
           /\ reg1' = "q26"
           /\ reg2' = "q27"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R114",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R114 == /\ pc = "R114"
        /\ /\ offset' = 32
           /\ reg1' = "q28"
           /\ reg2' = "q29"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R115",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R115 == /\ pc = "R115"
        /\ /\ offset' = 0
           /\ reg1' = "q30"
           /\ reg2' = "q31"
           /\ reg3' = "x0"
           /\ stack' = << [ procedure |->  "ldp16_add",
                            pc        |->  "R200",
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                        reg2_ld, reg3_l, offset_ld, addr_ld, ctx_start >>

R200 == /\ pc = "R200"
        /\ registers' = [registers EXCEPT !["x30"] = registers["sp"]]
        /\ pc' = "R_INT01"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

R_INT01 == /\ pc = "R_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "R300" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

R300 == /\ pc = "R300"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x0"
           /\ reg2_ld' = "x1"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R301",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R301 == /\ pc = "R301"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x2"
           /\ reg2_ld' = "x3"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R302",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R302 == /\ pc = "R302"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x4"
           /\ reg2_ld' = "x5"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R303",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R303 == /\ pc = "R303"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x6"
           /\ reg2_ld' = "x7"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R304",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R304 == /\ pc = "R304"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x8"
           /\ reg2_ld' = "x9"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R305",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R305 == /\ pc = "R305"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x10"
           /\ reg2_ld' = "x11"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R306",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R306 == /\ pc = "R306"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x12"
           /\ reg2_ld' = "x13"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R307",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R307 == /\ pc = "R307"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x14"
           /\ reg2_ld' = "x15"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R308",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R308 == /\ pc = "R308"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x16"
           /\ reg2_ld' = "x17"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R309",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R309 == /\ pc = "R309"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x18"
           /\ reg2_ld' = "x19"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R310",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R310 == /\ pc = "R310"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x20"
           /\ reg2_ld' = "x21"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R311",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R311 == /\ pc = "R311"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x22"
           /\ reg2_ld' = "x23"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R312",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R312 == /\ pc = "R312"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x24"
           /\ reg2_ld' = "x25"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R313",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R313 == /\ pc = "R313"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x26"
           /\ reg2_ld' = "x27"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R314",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R314 == /\ pc = "R314"
        /\ /\ offset_ld' = 16
           /\ reg1_ld' = "x28"
           /\ reg2_ld' = "x29"
           /\ reg3_l' = "x30"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R315",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp_add0_"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                        reg2_stp, reg3_st, offset_stp, addr_stp, reg1, reg2, 
                        reg3, offset, addr, ctx_start >>

R315 == /\ pc = "R315"
        /\ /\ offset_l' = 0
           /\ reg1_l' = "x30"
           /\ reg2_l' = "x30"
           /\ stack' = << [ procedure |->  "ldr_add",
                            pc        |->  "R_INT02",
                            addr_l    |->  addr_l,
                            reg1_l    |->  reg1_l,
                            reg2_l    |->  reg2_l,
                            offset_l  |->  offset_l ] >>
                        \o stack
        /\ addr_l' = defaultInitValue
        /\ pc' = "ldr_add0"
        /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                        offset_, addr_, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                        reg1_stp, reg2_stp, reg3_st, offset_stp, addr_stp, 
                        reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                        reg2, reg3, offset, addr, ctx_start >>

R_INT02 == /\ pc = "R_INT02"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "R400" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

R400 == /\ pc = "R400"
        /\ registers' = [registers EXCEPT !["sp"] = registers["sp"] + 800]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1_stp, reg2_stp, reg3_st, 
                        offset_stp, addr_stp, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

exception_restore_context == R000 \/ R001 \/ R002 \/ R100 \/ R101 \/ R102
                                \/ R103 \/ R104 \/ R105 \/ R106 \/ R107
                                \/ R108 \/ R109 \/ R110 \/ R111 \/ R112
                                \/ R113 \/ R114 \/ R115 \/ R200 \/ R_INT01
                                \/ R300 \/ R301 \/ R302 \/ R303 \/ R304
                                \/ R305 \/ R306 \/ R307 \/ R308 \/ R309
                                \/ R310 \/ R311 \/ R312 \/ R313 \/ R314
                                \/ R315 \/ R_INT02 \/ R400

H000 == /\ pc = "H000"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] + 1]
        /\ pc' = "H001"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H001 == /\ pc = "H001"
        /\ registers' = [registers EXCEPT !["x1"] = registers["x1"] + 1]
        /\ pc' = "H002"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H002 == /\ pc = "H002"
        /\ registers' = [registers EXCEPT !["x2"] = registers["x2"] + 1]
        /\ pc' = "H003"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H003 == /\ pc = "H003"
        /\ registers' = [registers EXCEPT !["x3"] = registers["x3"] + 1]
        /\ pc' = "H004"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H004 == /\ pc = "H004"
        /\ registers' = [registers EXCEPT !["x4"] = registers["x4"] + 1]
        /\ pc' = "H005"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H005 == /\ pc = "H005"
        /\ registers' = [registers EXCEPT !["x5"] = registers["x5"] + 1]
        /\ pc' = "H006"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H006 == /\ pc = "H006"
        /\ registers' = [registers EXCEPT !["x6"] = registers["x6"] + 1]
        /\ pc' = "H007"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H007 == /\ pc = "H007"
        /\ registers' = [registers EXCEPT !["x7"] = registers["x7"] + 1]
        /\ pc' = "H008"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H008 == /\ pc = "H008"
        /\ registers' = [registers EXCEPT !["x8"] = registers["x8"] + 1]
        /\ pc' = "H009"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H009 == /\ pc = "H009"
        /\ registers' = [registers EXCEPT !["x9"] = registers["x9"] + 1]
        /\ pc' = "H010"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H010 == /\ pc = "H010"
        /\ registers' = [registers EXCEPT !["x10"] = registers["x10"] + 1]
        /\ pc' = "H011"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H011 == /\ pc = "H011"
        /\ registers' = [registers EXCEPT !["x11"] = registers["x11"] + 1]
        /\ pc' = "H012"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H012 == /\ pc = "H012"
        /\ registers' = [registers EXCEPT !["x12"] = registers["x12"] + 1]
        /\ pc' = "H013"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H013 == /\ pc = "H013"
        /\ registers' = [registers EXCEPT !["x13"] = registers["x13"] + 1]
        /\ pc' = "H014"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H014 == /\ pc = "H014"
        /\ registers' = [registers EXCEPT !["x14"] = registers["x14"] + 1]
        /\ pc' = "H015"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H015 == /\ pc = "H015"
        /\ registers' = [registers EXCEPT !["x15"] = registers["x15"] + 1]
        /\ pc' = "H016"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H016 == /\ pc = "H016"
        /\ registers' = [registers EXCEPT !["x16"] = registers["x16"] + 1]
        /\ pc' = "H017"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H017 == /\ pc = "H017"
        /\ registers' = [registers EXCEPT !["x17"] = registers["x17"] + 1]
        /\ pc' = "H018"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H018 == /\ pc = "H018"
        /\ registers' = [registers EXCEPT !["x18"] = registers["x18"] + 1]
        /\ pc' = "H019"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H019 == /\ pc = "H019"
        /\ registers' = [registers EXCEPT !["x19"] = registers["x19"] + 1]
        /\ pc' = "H020"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H020 == /\ pc = "H020"
        /\ registers' = [registers EXCEPT !["x20"] = registers["x20"] + 1]
        /\ pc' = "H021"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H021 == /\ pc = "H021"
        /\ registers' = [registers EXCEPT !["x21"] = registers["x21"] + 1]
        /\ pc' = "H022"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H022 == /\ pc = "H022"
        /\ registers' = [registers EXCEPT !["x22"] = registers["x22"] + 1]
        /\ pc' = "H023"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H023 == /\ pc = "H023"
        /\ registers' = [registers EXCEPT !["x23"] = registers["x23"] + 1]
        /\ pc' = "H024"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H024 == /\ pc = "H024"
        /\ registers' = [registers EXCEPT !["x24"] = registers["x24"] + 1]
        /\ pc' = "H025"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H025 == /\ pc = "H025"
        /\ registers' = [registers EXCEPT !["x25"] = registers["x25"] + 1]
        /\ pc' = "H026"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H026 == /\ pc = "H026"
        /\ registers' = [registers EXCEPT !["x26"] = registers["x26"] + 1]
        /\ pc' = "H027"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H027 == /\ pc = "H027"
        /\ registers' = [registers EXCEPT !["x27"] = registers["x27"] + 1]
        /\ pc' = "H028"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H028 == /\ pc = "H028"
        /\ registers' = [registers EXCEPT !["x28"] = registers["x28"] + 1]
        /\ pc' = "H029"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H029 == /\ pc = "H029"
        /\ registers' = [registers EXCEPT !["x29"] = registers["x29"] + 1]
        /\ pc' = "H030"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H030 == /\ pc = "H030"
        /\ registers' = [registers EXCEPT !["x30"] = registers["x30"] + 1]
        /\ pc' = "H_INT00"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H_INT00 == /\ pc = "H_INT00"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "H100" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

H100 == /\ pc = "H100"
        /\ registers' = [registers EXCEPT !["q0"] = registers["q0"] + 1]
        /\ pc' = "H101"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H101 == /\ pc = "H101"
        /\ registers' = [registers EXCEPT !["q1"] = registers["q1"] + 1]
        /\ pc' = "H102"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H102 == /\ pc = "H102"
        /\ registers' = [registers EXCEPT !["q2"] = registers["q2"] + 1]
        /\ pc' = "H103"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H103 == /\ pc = "H103"
        /\ registers' = [registers EXCEPT !["q3"] = registers["q3"] + 1]
        /\ pc' = "H104"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H104 == /\ pc = "H104"
        /\ registers' = [registers EXCEPT !["q4"] = registers["q4"] + 1]
        /\ pc' = "H105"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H105 == /\ pc = "H105"
        /\ registers' = [registers EXCEPT !["q5"] = registers["q5"] + 1]
        /\ pc' = "H106"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H106 == /\ pc = "H106"
        /\ registers' = [registers EXCEPT !["q6"] = registers["q6"] + 1]
        /\ pc' = "H107"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H107 == /\ pc = "H107"
        /\ registers' = [registers EXCEPT !["q7"] = registers["q7"] + 1]
        /\ pc' = "H108"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H108 == /\ pc = "H108"
        /\ registers' = [registers EXCEPT !["q8"] = registers["q8"] + 1]
        /\ pc' = "H109"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H109 == /\ pc = "H109"
        /\ registers' = [registers EXCEPT !["q9"] = registers["q9"] + 1]
        /\ pc' = "H110"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H110 == /\ pc = "H110"
        /\ registers' = [registers EXCEPT !["q10"] = registers["q10"] + 1]
        /\ pc' = "H111"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H111 == /\ pc = "H111"
        /\ registers' = [registers EXCEPT !["q11"] = registers["q11"] + 1]
        /\ pc' = "H112"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H112 == /\ pc = "H112"
        /\ registers' = [registers EXCEPT !["q12"] = registers["q12"] + 1]
        /\ pc' = "H113"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H113 == /\ pc = "H113"
        /\ registers' = [registers EXCEPT !["q13"] = registers["q13"] + 1]
        /\ pc' = "H114"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H114 == /\ pc = "H114"
        /\ registers' = [registers EXCEPT !["q14"] = registers["q14"] + 1]
        /\ pc' = "H115"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H115 == /\ pc = "H115"
        /\ registers' = [registers EXCEPT !["q15"] = registers["q15"] + 1]
        /\ pc' = "H116"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H116 == /\ pc = "H116"
        /\ registers' = [registers EXCEPT !["q16"] = registers["q16"] + 1]
        /\ pc' = "H117"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H117 == /\ pc = "H117"
        /\ registers' = [registers EXCEPT !["q17"] = registers["q17"] + 1]
        /\ pc' = "H118"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H118 == /\ pc = "H118"
        /\ registers' = [registers EXCEPT !["q18"] = registers["q18"] + 1]
        /\ pc' = "H119"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H119 == /\ pc = "H119"
        /\ registers' = [registers EXCEPT !["q19"] = registers["q19"] + 1]
        /\ pc' = "H120"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H120 == /\ pc = "H120"
        /\ registers' = [registers EXCEPT !["q20"] = registers["q20"] + 1]
        /\ pc' = "H121"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H121 == /\ pc = "H121"
        /\ registers' = [registers EXCEPT !["q21"] = registers["q21"] + 1]
        /\ pc' = "H122"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H122 == /\ pc = "H122"
        /\ registers' = [registers EXCEPT !["q22"] = registers["q22"] + 1]
        /\ pc' = "H123"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H123 == /\ pc = "H123"
        /\ registers' = [registers EXCEPT !["q23"] = registers["q23"] + 1]
        /\ pc' = "H124"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H124 == /\ pc = "H124"
        /\ registers' = [registers EXCEPT !["q24"] = registers["q24"] + 1]
        /\ pc' = "H125"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H125 == /\ pc = "H125"
        /\ registers' = [registers EXCEPT !["q25"] = registers["q25"] + 1]
        /\ pc' = "H126"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H126 == /\ pc = "H126"
        /\ registers' = [registers EXCEPT !["q26"] = registers["q26"] + 1]
        /\ pc' = "H127"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H127 == /\ pc = "H127"
        /\ registers' = [registers EXCEPT !["q27"] = registers["q27"] + 1]
        /\ pc' = "H128"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H128 == /\ pc = "H128"
        /\ registers' = [registers EXCEPT !["q28"] = registers["q28"] + 1]
        /\ pc' = "H129"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H129 == /\ pc = "H129"
        /\ registers' = [registers EXCEPT !["q29"] = registers["q29"] + 1]
        /\ pc' = "H130"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H130 == /\ pc = "H130"
        /\ registers' = [registers EXCEPT !["q30"] = registers["q30"] + 1]
        /\ pc' = "H131"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H131 == /\ pc = "H131"
        /\ registers' = [registers EXCEPT !["q31"] = registers["q31"] + 1]
        /\ pc' = "H_INT01"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H_INT01 == /\ pc = "H_INT01"
           /\ stack' = << [ procedure |->  "interrupt",
                            pc        |->  "H200" ] >>
                        \o stack
           /\ pc' = "start_interrupt"
           /\ UNCHANGED << data_abort, stack_memory, registers, reg1_, reg2_, 
                           offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                           reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                           reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                           reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, 
                           reg3, offset, addr, ctx_start >>

H200 == /\ pc = "H200"
        /\ registers' = [registers EXCEPT !["elr"] = registers["elr"] + 1]
        /\ pc' = "H201"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H201 == /\ pc = "H201"
        /\ registers' = [registers EXCEPT !["spsr"] = registers["spsr"] + 1]
        /\ pc' = "H202"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H202 == /\ pc = "H202"
        /\ registers' = [registers EXCEPT !["fpsr"] = registers["fpsr"] + 1]
        /\ pc' = "H203"
        /\ UNCHANGED << data_abort, stack_memory, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_stp, reg2_stp, 
                        reg3_st, offset_stp, addr_stp, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, ctx_start >>

H203 == /\ pc = "H203"
        /\ registers' = [registers EXCEPT !["fpcr"] = registers["fpcr"] + 1]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << data_abort, stack_memory, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1_stp, reg2_stp, reg3_st, 
                        offset_stp, addr_stp, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        ctx_start >>

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
                         reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                         reg2_st, reg3_s, offset_st, addr_st, reg1_stp, 
                         reg2_stp, reg3_st, offset_stp, addr_stp, reg1_ld, 
                         reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                         offset, addr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == interrupt \/ data_abort_exception \/ str_add \/ ldr_add \/ stp
           \/ stp_add \/ stp16_add \/ ldp_add \/ ldp16_add \/ CALL_WITH_CONTEXT
           \/ exception_store_registers \/ exception_restore_context \/ handler
           \/ start
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
