----------------- MODULE context ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT SIZE_CONTEXT

(*--algorithm context

variables
    \* struct Context
    Context;

    ctx_start;

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
        sp |-> 300
    ];

define
    init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
end define;

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

\* str reg1, [reg2, offset]
\*
\* [reg2 + offset] = reg1;
procedure str(reg1, reg2, offset)
variables
    addr
begin
    str0:
        addr := registers[reg2] + offset;
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    str1:
        Context[addr] := registers[reg1];
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
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    ldr1:
        registers[reg1] := Context[addr];
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
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    str_add1:
        Context[addr] := registers[reg1];
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
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    ldr_add1:
        registers[reg1] := Context[addr];
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
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    stp1:
        Context[addr] := registers[reg1];
    stp2:
        Context[addr + 8] := registers[reg2];
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
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    ldp1:
        registers[reg1] := Context[addr];
    ldp2:
        registers[reg2] := Context[addr + 8];
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
        assert(0 <= addr /\ addr < SIZE_CONTEXT);
    ldp_add1:
        registers[reg1] := Context[addr];
    ldp_add2:
        registers[reg2] := Context[addr + 8];
    ldp_add3:
        registers[reg3] := addr + offset;
        return;
end procedure;

procedure save_context()
begin
    \* Store floating-point registers.
    S00: call str_add( "q0", "x0", 16);
    S01: call str_add( "q1", "x0", 16);
    S02: call str_add( "q2", "x0", 16);
    S03: call str_add( "q3", "x0", 16);
    S04: call str_add( "q4", "x0", 16);
    S05: call str_add( "q5", "x0", 16);
    S06: call str_add( "q6", "x0", 16);
    S07: call str_add( "q7", "x0", 16);
    S08: call str_add( "q8", "x0", 16);
    S09: call str_add( "q9", "x0", 16);
    S10: call str_add("q10", "x0", 16);
    S11: call str_add("q11", "x0", 16);
    S12: call str_add("q12", "x0", 16);
    S13: call str_add("q13", "x0", 16);
    S14: call str_add("q14", "x0", 16);
    S15: call str_add("q15", "x0", 16);
    S16: call str_add("q16", "x0", 16);
    S17: call str_add("q17", "x0", 16);
    S18: call str_add("q18", "x0", 16);
    S19: call str_add("q19", "x0", 16);
    S20: call str_add("q20", "x0", 16);
    S21: call str_add("q21", "x0", 16);
    S22: call str_add("q22", "x0", 16);
    S23: call str_add("q23", "x0", 16);
    S24: call str_add("q24", "x0", 16);
    S25: call str_add("q25", "x0", 16);
    S26: call str_add("q26", "x0", 16);
    S27: call str_add("q27", "x0", 16);
    S28: call str_add("q28", "x0", 16);
    S29: call str_add("q29", "x0", 16);
    S30: call str_add("q30", "x0", 16);
    S31: call str_add("q31", "x0", 16);

    \* Store general purpose registers.
    S100: call stp( "x2",  "x3", "x0", 16 * 2);
    S101: call stp( "x4",  "x5", "x0", 16 * 3);
    S102: call stp( "x6",  "x7", "x0", 16 * 4);
    S103: call stp( "x8",  "x9", "x0", 16 * 5);
    S104: call stp("x10", "x11", "x0", 16 * 6);
    S105: call stp("x12", "x13", "x0", 16 * 7);
    S106: call stp("x14", "x15", "x0", 16 * 8);
    S107: call stp("x16", "x17", "x0", 16 * 9);
    S108: call stp("x18", "x19", "x0", 16 * 10);
    S109: call stp("x20", "x21", "x0", 16 * 11);
    S110: call stp("x22", "x23", "x0", 16 * 12);
    S111: call stp("x24", "x25", "x0", 16 * 13);
    S112: call stp("x26", "x27", "x0", 16 * 14);
    S113: call stp("x28", "x29", "x0", 16 * 15);
    S114: call str("x30", "x0", 16 * 16);

    \* Store FPSR and FPCR registers.
    S200: msr("x9", "fpsr");
    S201: msr("x10", "fpcr");
    S202: call stp("x9", "x10", "x0", 0);

    \* Store SPSR.
    S203: add("x0", "x0", 16 * 17);
    S204: mrs("x9", "spsr");
    S205: call str("x9", "x0", 0);

    \* Store SP.
    S206: mov("x9", "sp");
    S207: call str("x9", "x0", 8);

    \* Store x0 and x1.
    S208: sub("x9", "x0", 16 * 16);
    S209: sub("x0", "x0", 16 * 49);
    S210: call stp("x0", "x1", "x9", 0);

    return;
end procedure;

procedure restore_context()
begin
    \* Load floating-point registers.
    R00: call ldr_add( "q0", "x0", 16);
    R01: call ldr_add( "q1", "x0", 16);
    R02: call ldr_add( "q2", "x0", 16);
    R03: call ldr_add( "q3", "x0", 16);
    R04: call ldr_add( "q4", "x0", 16);
    R05: call ldr_add( "q5", "x0", 16);
    R06: call ldr_add( "q6", "x0", 16);
    R07: call ldr_add( "q7", "x0", 16);
    R08: call ldr_add( "q8", "x0", 16);
    R09: call ldr_add( "q9", "x0", 16);
    R10: call ldr_add("q10", "x0", 16);
    R11: call ldr_add("q11", "x0", 16);
    R12: call ldr_add("q12", "x0", 16);
    R13: call ldr_add("q13", "x0", 16);
    R14: call ldr_add("q14", "x0", 16);
    R15: call ldr_add("q15", "x0", 16);
    R16: call ldr_add("q16", "x0", 16);
    R17: call ldr_add("q17", "x0", 16);
    R18: call ldr_add("q18", "x0", 16);
    R19: call ldr_add("q19", "x0", 16);
    R20: call ldr_add("q20", "x0", 16);
    R21: call ldr_add("q21", "x0", 16);
    R22: call ldr_add("q22", "x0", 16);
    R23: call ldr_add("q23", "x0", 16);
    R24: call ldr_add("q24", "x0", 16);
    R25: call ldr_add("q25", "x0", 16);
    R26: call ldr_add("q26", "x0", 16);
    R27: call ldr_add("q27", "x0", 16);
    R28: call ldr_add("q28", "x0", 16);
    R29: call ldr_add("q29", "x0", 16);
    R30: call ldr_add("q30", "x0", 16);
    R31: call ldr_add("q31", "x0", 16);

    \* Load general purpose registers.
    R100: call ldp( "x4",  "x5", "x0", 16 * 3);
    R101: call ldp( "x6",  "x7", "x0", 16 * 4);
    R102: call ldp( "x8",  "x9", "x0", 16 * 5);
    R103: call ldp("x10", "x11", "x0", 16 * 6);
    R104: call ldp("x12", "x13", "x0", 16 * 7);
    R105: call ldp("x14", "x15", "x0", 16 * 8);
    R106: call ldp("x16", "x17", "x0", 16 * 9);
    R107: call ldp("x18", "x19", "x0", 16 * 10);
    R108: call ldp("x20", "x21", "x0", 16 * 11);
    R109: call ldp("x22", "x23", "x0", 16 * 12);
    R110: call ldp("x24", "x25", "x0", 16 * 13);
    R111: call ldp("x26", "x27", "x0", 16 * 14);
    R112: call ldp("x28", "x29", "x0", 16 * 15);
    R113: call ldr("x30", "x0", 16 * 16);

    \* Load FPSR and FPCR registers.
    R200: call ldp("x2", "x3", "x0", 0);
    R201: msr("fpsr", "x2");
    R202: msr("fpcr", "x3");

    \* Load SPSR.
    R203: add("x0", "x0", 16 * 17);
    R204: call ldr("x1", "x0", 0);
    R205: msr("spsr", "x1");

    \* Load SP.
    R206: call ldr("x2", "x0", 8);
    R207: mov("sp", "x2");

    \* ELR == 0?
    R208: call ldr("x2", "x0", -8);
    R209: sub("x0", "x0", 16 * 16);

    if registers["x2"] /= 0 then
        R210: msr("elr", "x2");

        \* Load x0 to x2.
        R211: call ldp("x2", "x3", "x0", 16);
        R212: call ldp("x0", "x1", "x0", 0);
    else
        \* Load x0 to x2.
        R213: call ldp("x2", "x3", "x0", 16);
        R214: call ldp("x0", "x1", "x0", 0);
    end if;

    R215: return;
end procedure;

procedure check_erl_null()
variables
    ctx;
begin
    start_check_elr_null:
        Context := init_context;
        registers["x0"] := 0;

    elr_null0:
        registers["elr"] := 0;
        ctx := registers;

    elr_null1:
        call save_context();

    elr_null2:
        registers["x0"] := 0;
        call restore_context();

    elr_null3:
        assert(registers = ctx);

    return;
end procedure;


procedure check_elr_not_null()
variables
    ctx;
begin
    start_elr_not_null:
        Context := init_context;
        registers["x0"] := 0;

    elr_not_null0:
        registers["elr"] := 200;
        Context[776] := 200; \* elr := 200
        ctx_start := registers;

    elr_not_null1:
        call save_context();

    elr_not_null2:
        registers["x0"] := 0;
        call restore_context();

    elr_not_null3:
        assert(registers = ctx_start);

    return;
end procedure;

begin
    check1:
        call check_erl_null();

    check2:
        call check_elr_not_null();
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "d25eee68" /\ chksum(tla) = "8086f17d")
\* Procedure variable addr of procedure str at line 141 col 5 changed to addr_
\* Procedure variable addr of procedure ldr at line 156 col 5 changed to addr_l
\* Procedure variable addr of procedure str_add at line 172 col 5 changed to addr_s
\* Procedure variable addr of procedure ldr_add at line 189 col 5 changed to addr_ld
\* Procedure variable addr of procedure stp at line 207 col 5 changed to addr_st
\* Procedure variable addr of procedure ldp at line 225 col 5 changed to addr_ldp
\* Procedure variable ctx of procedure check_erl_null at line 420 col 5 changed to ctx_
\* Parameter reg1 of procedure str at line 139 col 15 changed to reg1_
\* Parameter reg2 of procedure str at line 139 col 21 changed to reg2_
\* Parameter offset of procedure str at line 139 col 27 changed to offset_
\* Parameter reg1 of procedure ldr at line 154 col 15 changed to reg1_l
\* Parameter reg2 of procedure ldr at line 154 col 21 changed to reg2_l
\* Parameter offset of procedure ldr at line 154 col 27 changed to offset_l
\* Parameter reg1 of procedure str_add at line 170 col 19 changed to reg1_s
\* Parameter reg2 of procedure str_add at line 170 col 25 changed to reg2_s
\* Parameter offset of procedure str_add at line 170 col 31 changed to offset_s
\* Parameter reg1 of procedure ldr_add at line 187 col 19 changed to reg1_ld
\* Parameter reg2 of procedure ldr_add at line 187 col 25 changed to reg2_ld
\* Parameter offset of procedure ldr_add at line 187 col 31 changed to offset_ld
\* Parameter reg1 of procedure stp at line 205 col 15 changed to reg1_st
\* Parameter reg2 of procedure stp at line 205 col 21 changed to reg2_st
\* Parameter reg3 of procedure stp at line 205 col 27 changed to reg3_
\* Parameter offset of procedure stp at line 205 col 33 changed to offset_st
\* Parameter reg1 of procedure ldp at line 223 col 15 changed to reg1_ldp
\* Parameter reg2 of procedure ldp at line 223 col 21 changed to reg2_ldp
\* Parameter reg3 of procedure ldp at line 223 col 27 changed to reg3_l
\* Parameter offset of procedure ldp at line 223 col 33 changed to offset_ldp
CONSTANT defaultInitValue
VARIABLES Context, ctx_start, registers, pc, stack

(* define statement *)
init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]

VARIABLES reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
          reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
          addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
          reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
          addr, ctx_, ctx

vars == << Context, ctx_start, registers, pc, stack, reg1_, reg2_, offset_, 
           addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, offset_s, 
           addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
           reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
           addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

Init == (* Global variables *)
        /\ Context = defaultInitValue
        /\ ctx_start = defaultInitValue
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
                       
                       
                           sp |-> 300
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
        (* Procedure check_erl_null *)
        /\ ctx_ = defaultInitValue
        (* Procedure check_elr_not_null *)
        /\ ctx = defaultInitValue
        /\ stack = << >>
        /\ pc = "check1"

str0 == /\ pc = "str0"
        /\ addr_' = registers[reg2_] + offset_
        /\ Assert((0 <= addr_' /\ addr_' < SIZE_CONTEXT), 
                  "Failure of assertion at line 145, column 9.")
        /\ pc' = "str1"
        /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                        offset_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

str1 == /\ pc = "str1"
        /\ Context' = [Context EXCEPT ![addr_] = registers[reg1_]]
        /\ pc' = Head(stack).pc
        /\ addr_' = Head(stack).addr_
        /\ reg1_' = Head(stack).reg1_
        /\ reg2_' = Head(stack).reg2_
        /\ offset_' = Head(stack).offset_
        /\ stack' = Tail(stack)
        /\ UNCHANGED << ctx_start, registers, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

str == str0 \/ str1

ldr0 == /\ pc = "ldr0"
        /\ addr_l' = registers[reg2_l] + offset_l
        /\ Assert((0 <= addr_l' /\ addr_l' < SIZE_CONTEXT), 
                  "Failure of assertion at line 160, column 9.")
        /\ pc' = "ldr1"
        /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

ldr1 == /\ pc = "ldr1"
        /\ registers' = [registers EXCEPT ![reg1_l] = Context[addr_l]]
        /\ pc' = Head(stack).pc
        /\ addr_l' = Head(stack).addr_l
        /\ reg1_l' = Head(stack).reg1_l
        /\ reg2_l' = Head(stack).reg2_l
        /\ offset_l' = Head(stack).offset_l
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, ctx_start, reg1_, reg2_, offset_, addr_, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

ldr == ldr0 \/ ldr1

str_add0 == /\ pc = "str_add0"
            /\ addr_s' = registers[reg2_s]
            /\ Assert((0 <= addr_s' /\ addr_s' < SIZE_CONTEXT), 
                      "Failure of assertion at line 176, column 9.")
            /\ pc' = "str_add1"
            /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_, ctx >>

str_add1 == /\ pc = "str_add1"
            /\ Context' = [Context EXCEPT ![addr_s] = registers[reg1_s]]
            /\ registers' = [registers EXCEPT ![reg2_s] = addr_s + offset_s]
            /\ pc' = Head(stack).pc
            /\ addr_s' = Head(stack).addr_s
            /\ reg1_s' = Head(stack).reg1_s
            /\ reg2_s' = Head(stack).reg2_s
            /\ offset_s' = Head(stack).offset_s
            /\ stack' = Tail(stack)
            /\ UNCHANGED << ctx_start, reg1_, reg2_, offset_, addr_, reg1_l, 
                            reg2_l, offset_l, addr_l, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_, ctx >>

str_add == str_add0 \/ str_add1

ldr_add0 == /\ pc = "ldr_add0"
            /\ addr_ld' = registers[reg2_ld]
            /\ Assert((0 <= addr_ld' /\ addr_ld' < SIZE_CONTEXT), 
                      "Failure of assertion at line 193, column 9.")
            /\ pc' = "ldr_add1"
            /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, reg1_st, reg2_st, reg3_, offset_st, 
                            addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                            addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, 
                            ctx >>

ldr_add1 == /\ pc = "ldr_add1"
            /\ registers' = [registers EXCEPT ![reg1_ld] = Context[addr_ld]]
            /\ pc' = "ldr_add2"
            /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_, ctx >>

ldr_add2 == /\ pc = "ldr_add2"
            /\ registers' = [registers EXCEPT ![reg2_ld] = addr_ld + offset_ld]
            /\ pc' = Head(stack).pc
            /\ addr_ld' = Head(stack).addr_ld
            /\ reg1_ld' = Head(stack).reg1_ld
            /\ reg2_ld' = Head(stack).reg2_ld
            /\ offset_ld' = Head(stack).offset_ld
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, ctx_start, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            offset_s, addr_s, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_, ctx >>

ldr_add == ldr_add0 \/ ldr_add1 \/ ldr_add2

stp0 == /\ pc = "stp0"
        /\ addr_st' = registers[reg3_] + offset_st
        /\ Assert((0 <= addr_st' /\ addr_st' < SIZE_CONTEXT), 
                  "Failure of assertion at line 211, column 9.")
        /\ pc' = "stp1"
        /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

stp1 == /\ pc = "stp1"
        /\ Context' = [Context EXCEPT ![addr_st] = registers[reg1_st]]
        /\ pc' = "stp2"
        /\ UNCHANGED << ctx_start, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

stp2 == /\ pc = "stp2"
        /\ Context' = [Context EXCEPT ![addr_st + 8] = registers[reg2_st]]
        /\ pc' = Head(stack).pc
        /\ addr_st' = Head(stack).addr_st
        /\ reg1_st' = Head(stack).reg1_st
        /\ reg2_st' = Head(stack).reg2_st
        /\ reg3_' = Head(stack).reg3_
        /\ offset_st' = Head(stack).offset_st
        /\ stack' = Tail(stack)
        /\ UNCHANGED << ctx_start, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

stp == stp0 \/ stp1 \/ stp2

ldp0 == /\ pc = "ldp0"
        /\ addr_ldp' = registers[reg3_l] + offset_ldp
        /\ Assert((0 <= addr_ldp' /\ addr_ldp' < SIZE_CONTEXT), 
                  "Failure of assertion at line 229, column 9.")
        /\ pc' = "ldp1"
        /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                        offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                        offset_ld, addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                        addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

ldp1 == /\ pc = "ldp1"
        /\ registers' = [registers EXCEPT ![reg1_ldp] = Context[addr_ldp]]
        /\ pc' = "ldp2"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

ldp2 == /\ pc = "ldp2"
        /\ registers' = [registers EXCEPT ![reg2_ldp] = Context[addr_ldp + 8]]
        /\ pc' = Head(stack).pc
        /\ addr_ldp' = Head(stack).addr_ldp
        /\ reg1_ldp' = Head(stack).reg1_ldp
        /\ reg2_ldp' = Head(stack).reg2_ldp
        /\ reg3_l' = Head(stack).reg3_l
        /\ offset_ldp' = Head(stack).offset_ldp
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, ctx_start, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, addr_ld, 
                        reg1_st, reg2_st, reg3_, offset_st, addr_st, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

ldp == ldp0 \/ ldp1 \/ ldp2

ldp_add0 == /\ pc = "ldp_add0"
            /\ addr' = registers[reg3]
            /\ Assert((0 <= addr' /\ addr' < SIZE_CONTEXT), 
                      "Failure of assertion at line 248, column 9.")
            /\ pc' = "ldp_add1"
            /\ UNCHANGED << Context, ctx_start, registers, stack, reg1_, reg2_, 
                            offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                            reg1_s, reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            ctx_, ctx >>

ldp_add1 == /\ pc = "ldp_add1"
            /\ registers' = [registers EXCEPT ![reg1] = Context[addr]]
            /\ pc' = "ldp_add2"
            /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_, ctx >>

ldp_add2 == /\ pc = "ldp_add2"
            /\ registers' = [registers EXCEPT ![reg2] = Context[addr + 8]]
            /\ pc' = "ldp_add3"
            /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                            offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                            offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                            offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                            addr, ctx_, ctx >>

ldp_add3 == /\ pc = "ldp_add3"
            /\ registers' = [registers EXCEPT ![reg3] = addr + offset]
            /\ pc' = Head(stack).pc
            /\ addr' = Head(stack).addr
            /\ reg1' = Head(stack).reg1
            /\ reg2' = Head(stack).reg2
            /\ reg3' = Head(stack).reg3
            /\ offset' = Head(stack).offset
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, ctx_start, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                            addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                            addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                            addr_ldp, ctx_, ctx >>

ldp_add == ldp_add0 \/ ldp_add1 \/ ldp_add2 \/ ldp_add3

S00 == /\ pc = "S00"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q0"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S01",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S01 == /\ pc = "S01"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q1"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S02",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S02 == /\ pc = "S02"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q2"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S03",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S03 == /\ pc = "S03"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q3"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S04",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S04 == /\ pc = "S04"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q4"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S05",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S05 == /\ pc = "S05"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q5"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S06",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S06 == /\ pc = "S06"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q6"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S07",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S07 == /\ pc = "S07"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q7"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S08",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S08 == /\ pc = "S08"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q8"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S09",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S09 == /\ pc = "S09"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q9"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S10",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S10 == /\ pc = "S10"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q10"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S11",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S11 == /\ pc = "S11"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q11"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S12",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S12 == /\ pc = "S12"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q12"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S13",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S13 == /\ pc = "S13"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q13"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S14",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S14 == /\ pc = "S14"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q14"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S15",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S15 == /\ pc = "S15"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q15"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S16",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S16 == /\ pc = "S16"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q16"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S17",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S17 == /\ pc = "S17"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q17"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S18",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S18 == /\ pc = "S18"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q18"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S19",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S19 == /\ pc = "S19"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q19"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S20",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S20 == /\ pc = "S20"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q20"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S21",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S21 == /\ pc = "S21"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q21"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S22",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S22 == /\ pc = "S22"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q22"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S23",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S23 == /\ pc = "S23"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q23"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S24",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S24 == /\ pc = "S24"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q24"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S25",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S25 == /\ pc = "S25"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q25"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S26",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S26 == /\ pc = "S26"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q26"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S27",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S27 == /\ pc = "S27"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q27"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S28",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S28 == /\ pc = "S28"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q28"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S29",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S29 == /\ pc = "S29"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q29"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S30",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S30 == /\ pc = "S30"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q30"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S31",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S31 == /\ pc = "S31"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "q31"
          /\ reg2_s' = "x0"
          /\ stack' = << [ procedure |->  "str_add",
                           pc        |->  "S100",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "str_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_ld, 
                       reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                       offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                       offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                       ctx_, ctx >>

S100 == /\ pc = "S100"
        /\ /\ offset_st' = 16 * 2
           /\ reg1_st' = "x2"
           /\ reg2_st' = "x3"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S101",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S101 == /\ pc = "S101"
        /\ /\ offset_st' = 16 * 3
           /\ reg1_st' = "x4"
           /\ reg2_st' = "x5"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S102",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S102 == /\ pc = "S102"
        /\ /\ offset_st' = 16 * 4
           /\ reg1_st' = "x6"
           /\ reg2_st' = "x7"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S103",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S103 == /\ pc = "S103"
        /\ /\ offset_st' = 16 * 5
           /\ reg1_st' = "x8"
           /\ reg2_st' = "x9"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S104",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S104 == /\ pc = "S104"
        /\ /\ offset_st' = 16 * 6
           /\ reg1_st' = "x10"
           /\ reg2_st' = "x11"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S105",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S105 == /\ pc = "S105"
        /\ /\ offset_st' = 16 * 7
           /\ reg1_st' = "x12"
           /\ reg2_st' = "x13"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S106",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S106 == /\ pc = "S106"
        /\ /\ offset_st' = 16 * 8
           /\ reg1_st' = "x14"
           /\ reg2_st' = "x15"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S107",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S107 == /\ pc = "S107"
        /\ /\ offset_st' = 16 * 9
           /\ reg1_st' = "x16"
           /\ reg2_st' = "x17"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S108",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S108 == /\ pc = "S108"
        /\ /\ offset_st' = 16 * 10
           /\ reg1_st' = "x18"
           /\ reg2_st' = "x19"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S109",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S109 == /\ pc = "S109"
        /\ /\ offset_st' = 16 * 11
           /\ reg1_st' = "x20"
           /\ reg2_st' = "x21"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S110",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S110 == /\ pc = "S110"
        /\ /\ offset_st' = 16 * 12
           /\ reg1_st' = "x22"
           /\ reg2_st' = "x23"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S111",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S111 == /\ pc = "S111"
        /\ /\ offset_st' = 16 * 13
           /\ reg1_st' = "x24"
           /\ reg2_st' = "x25"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S112",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S112 == /\ pc = "S112"
        /\ /\ offset_st' = 16 * 14
           /\ reg1_st' = "x26"
           /\ reg2_st' = "x27"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S113",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S113 == /\ pc = "S113"
        /\ /\ offset_st' = 16 * 15
           /\ reg1_st' = "x28"
           /\ reg2_st' = "x29"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S114",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S114 == /\ pc = "S114"
        /\ /\ offset_' = 16 * 16
           /\ reg1_' = "x30"
           /\ reg2_' = "x0"
           /\ stack' = << [ procedure |->  "str",
                            pc        |->  "S200",
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "str0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

S200 == /\ pc = "S200"
        /\ registers' = [registers EXCEPT !["x9"] = registers["fpsr"]]
        /\ pc' = "S201"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S201 == /\ pc = "S201"
        /\ registers' = [registers EXCEPT !["x10"] = registers["fpcr"]]
        /\ pc' = "S202"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S202 == /\ pc = "S202"
        /\ /\ offset_st' = 0
           /\ reg1_st' = "x9"
           /\ reg2_st' = "x10"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S203",
                            addr_st   |->  addr_st,
                            reg1_st   |->  reg1_st,
                            reg2_st   |->  reg2_st,
                            reg3_     |->  reg3_,
                            offset_st |->  offset_st ] >>
                        \o stack
        /\ addr_st' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

S203 == /\ pc = "S203"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] + (16 * 17)]
        /\ pc' = "S204"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S204 == /\ pc = "S204"
        /\ registers' = [registers EXCEPT !["x9"] = registers["spsr"]]
        /\ pc' = "S205"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S205 == /\ pc = "S205"
        /\ /\ offset_' = 0
           /\ reg1_' = "x9"
           /\ reg2_' = "x0"
           /\ stack' = << [ procedure |->  "str",
                            pc        |->  "S206",
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "str0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

S206 == /\ pc = "S206"
        /\ registers' = [registers EXCEPT !["x9"] = registers["sp"]]
        /\ pc' = "S207"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S207 == /\ pc = "S207"
        /\ /\ offset_' = 8
           /\ reg1_' = "x9"
           /\ reg2_' = "x0"
           /\ stack' = << [ procedure |->  "str",
                            pc        |->  "S208",
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "str0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                        reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                        reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

S208 == /\ pc = "S208"
        /\ registers' = [registers EXCEPT !["x9"] = registers["x0"] - (16 * 16)]
        /\ pc' = "S209"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S209 == /\ pc = "S209"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] - (16 * 49)]
        /\ pc' = "S210"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

S210 == /\ pc = "S210"
        /\ /\ offset_st' = 0
           /\ reg1_st' = "x0"
           /\ reg2_st' = "x1"
           /\ reg3_' = "x9"
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
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                        addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

save_context == S00 \/ S01 \/ S02 \/ S03 \/ S04 \/ S05 \/ S06 \/ S07 \/ S08
                   \/ S09 \/ S10 \/ S11 \/ S12 \/ S13 \/ S14 \/ S15 \/ S16
                   \/ S17 \/ S18 \/ S19 \/ S20 \/ S21 \/ S22 \/ S23 \/ S24
                   \/ S25 \/ S26 \/ S27 \/ S28 \/ S29 \/ S30 \/ S31 \/ S100
                   \/ S101 \/ S102 \/ S103 \/ S104 \/ S105 \/ S106 \/ S107
                   \/ S108 \/ S109 \/ S110 \/ S111 \/ S112 \/ S113 \/ S114
                   \/ S200 \/ S201 \/ S202 \/ S203 \/ S204 \/ S205 \/ S206
                   \/ S207 \/ S208 \/ S209 \/ S210

R00 == /\ pc = "R00"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q0"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R01",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R01 == /\ pc = "R01"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q1"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R02",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R02 == /\ pc = "R02"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q2"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R03",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R03 == /\ pc = "R03"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q3"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R04",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R04 == /\ pc = "R04"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q4"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R05",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R05 == /\ pc = "R05"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q5"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R06",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R06 == /\ pc = "R06"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q6"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R07",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R07 == /\ pc = "R07"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q7"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R08",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R08 == /\ pc = "R08"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q8"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R09",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R09 == /\ pc = "R09"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q9"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R10",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R10 == /\ pc = "R10"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q10"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R11",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R11 == /\ pc = "R11"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q11"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R12",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R12 == /\ pc = "R12"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q12"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R13",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R13 == /\ pc = "R13"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q13"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R14",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R14 == /\ pc = "R14"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q14"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R15",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R15 == /\ pc = "R15"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q15"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R16",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R16 == /\ pc = "R16"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q16"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R17",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R17 == /\ pc = "R17"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q17"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R18",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R18 == /\ pc = "R18"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q18"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R19",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R19 == /\ pc = "R19"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q19"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R20",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R20 == /\ pc = "R20"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q20"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R21",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R21 == /\ pc = "R21"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q21"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R22",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R22 == /\ pc = "R22"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q22"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R23",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R23 == /\ pc = "R23"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q23"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R24",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R24 == /\ pc = "R24"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q24"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R25",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R25 == /\ pc = "R25"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q25"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R26",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R26 == /\ pc = "R26"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q26"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R27",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R27 == /\ pc = "R27"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q27"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R28",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R28 == /\ pc = "R28"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q28"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R29",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R29 == /\ pc = "R29"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q29"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R30",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R30 == /\ pc = "R30"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q30"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R31",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R31 == /\ pc = "R31"
       /\ /\ offset_ld' = 16
          /\ reg1_ld' = "q31"
          /\ reg2_ld' = "x0"
          /\ stack' = << [ procedure |->  "ldr_add",
                           pc        |->  "R100",
                           addr_ld   |->  addr_ld,
                           reg1_ld   |->  reg1_ld,
                           reg2_ld   |->  reg2_ld,
                           offset_ld |->  offset_ld ] >>
                       \o stack
       /\ addr_ld' = defaultInitValue
       /\ pc' = "ldr_add0"
       /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                       addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_, offset_st, 
                       addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                       addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R100 == /\ pc = "R100"
        /\ /\ offset_ldp' = 16 * 3
           /\ reg1_ldp' = "x4"
           /\ reg2_ldp' = "x5"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R101",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R101 == /\ pc = "R101"
        /\ /\ offset_ldp' = 16 * 4
           /\ reg1_ldp' = "x6"
           /\ reg2_ldp' = "x7"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R102",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R102 == /\ pc = "R102"
        /\ /\ offset_ldp' = 16 * 5
           /\ reg1_ldp' = "x8"
           /\ reg2_ldp' = "x9"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R103",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R103 == /\ pc = "R103"
        /\ /\ offset_ldp' = 16 * 6
           /\ reg1_ldp' = "x10"
           /\ reg2_ldp' = "x11"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R104",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R104 == /\ pc = "R104"
        /\ /\ offset_ldp' = 16 * 7
           /\ reg1_ldp' = "x12"
           /\ reg2_ldp' = "x13"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R105",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R105 == /\ pc = "R105"
        /\ /\ offset_ldp' = 16 * 8
           /\ reg1_ldp' = "x14"
           /\ reg2_ldp' = "x15"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R106",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R106 == /\ pc = "R106"
        /\ /\ offset_ldp' = 16 * 9
           /\ reg1_ldp' = "x16"
           /\ reg2_ldp' = "x17"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R107",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R107 == /\ pc = "R107"
        /\ /\ offset_ldp' = 16 * 10
           /\ reg1_ldp' = "x18"
           /\ reg2_ldp' = "x19"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R108",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R108 == /\ pc = "R108"
        /\ /\ offset_ldp' = 16 * 11
           /\ reg1_ldp' = "x20"
           /\ reg2_ldp' = "x21"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R109",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R109 == /\ pc = "R109"
        /\ /\ offset_ldp' = 16 * 12
           /\ reg1_ldp' = "x22"
           /\ reg2_ldp' = "x23"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R110",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R110 == /\ pc = "R110"
        /\ /\ offset_ldp' = 16 * 13
           /\ reg1_ldp' = "x24"
           /\ reg2_ldp' = "x25"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R111",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R111 == /\ pc = "R111"
        /\ /\ offset_ldp' = 16 * 14
           /\ reg1_ldp' = "x26"
           /\ reg2_ldp' = "x27"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R112",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R112 == /\ pc = "R112"
        /\ /\ offset_ldp' = 16 * 15
           /\ reg1_ldp' = "x28"
           /\ reg2_ldp' = "x29"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R113",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R113 == /\ pc = "R113"
        /\ /\ offset_l' = 16 * 16
           /\ reg1_l' = "x30"
           /\ reg2_l' = "x0"
           /\ stack' = << [ procedure |->  "ldr",
                            pc        |->  "R200",
                            addr_l    |->  addr_l,
                            reg1_l    |->  reg1_l,
                            reg2_l    |->  reg2_l,
                            offset_l  |->  offset_l ] >>
                        \o stack
        /\ addr_l' = defaultInitValue
        /\ pc' = "ldr0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                        reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                        offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

R200 == /\ pc = "R200"
        /\ /\ offset_ldp' = 0
           /\ reg1_ldp' = "x2"
           /\ reg2_ldp' = "x3"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R201",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R201 == /\ pc = "R201"
        /\ registers' = [registers EXCEPT !["fpsr"] = registers["x2"]]
        /\ pc' = "R202"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R202 == /\ pc = "R202"
        /\ registers' = [registers EXCEPT !["fpcr"] = registers["x3"]]
        /\ pc' = "R203"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R203 == /\ pc = "R203"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] + (16 * 17)]
        /\ pc' = "R204"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R204 == /\ pc = "R204"
        /\ /\ offset_l' = 0
           /\ reg1_l' = "x1"
           /\ reg2_l' = "x0"
           /\ stack' = << [ procedure |->  "ldr",
                            pc        |->  "R205",
                            addr_l    |->  addr_l,
                            reg1_l    |->  reg1_l,
                            reg2_l    |->  reg2_l,
                            offset_l  |->  offset_l ] >>
                        \o stack
        /\ addr_l' = defaultInitValue
        /\ pc' = "ldr0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                        reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                        offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

R205 == /\ pc = "R205"
        /\ registers' = [registers EXCEPT !["spsr"] = registers["x1"]]
        /\ pc' = "R206"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R206 == /\ pc = "R206"
        /\ /\ offset_l' = 8
           /\ reg1_l' = "x2"
           /\ reg2_l' = "x0"
           /\ stack' = << [ procedure |->  "ldr",
                            pc        |->  "R207",
                            addr_l    |->  addr_l,
                            reg1_l    |->  reg1_l,
                            reg2_l    |->  reg2_l,
                            offset_l  |->  offset_l ] >>
                        \o stack
        /\ addr_l' = defaultInitValue
        /\ pc' = "ldr0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                        reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                        offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

R207 == /\ pc = "R207"
        /\ registers' = [registers EXCEPT !["sp"] = registers["x2"]]
        /\ pc' = "R208"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R208 == /\ pc = "R208"
        /\ /\ offset_l' = -8
           /\ reg1_l' = "x2"
           /\ reg2_l' = "x0"
           /\ stack' = << [ procedure |->  "ldr",
                            pc        |->  "R209",
                            addr_l    |->  addr_l,
                            reg1_l    |->  reg1_l,
                            reg2_l    |->  reg2_l,
                            offset_l  |->  offset_l ] >>
                        \o stack
        /\ addr_l' = defaultInitValue
        /\ pc' = "ldr0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                        reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                        offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                        offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                        ctx_, ctx >>

R209 == /\ pc = "R209"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] - (16 * 16)]
        /\ IF registers'["x2"] /= 0
              THEN /\ pc' = "R210"
              ELSE /\ pc' = "R213"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R210 == /\ pc = "R210"
        /\ registers' = [registers EXCEPT !["elr"] = registers["x2"]]
        /\ pc' = "R211"
        /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

R211 == /\ pc = "R211"
        /\ /\ offset_ldp' = 16
           /\ reg1_ldp' = "x2"
           /\ reg2_ldp' = "x3"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R212",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R212 == /\ pc = "R212"
        /\ /\ offset_ldp' = 0
           /\ reg1_ldp' = "x0"
           /\ reg2_ldp' = "x1"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R215",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R213 == /\ pc = "R213"
        /\ /\ offset_ldp' = 16
           /\ reg1_ldp' = "x2"
           /\ reg2_ldp' = "x3"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R214",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R214 == /\ pc = "R214"
        /\ /\ offset_ldp' = 0
           /\ reg1_ldp' = "x0"
           /\ reg2_ldp' = "x1"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R215",
                            addr_ldp  |->  addr_ldp,
                            reg1_ldp  |->  reg1_ldp,
                            reg2_ldp  |->  reg2_ldp,
                            reg3_l    |->  reg3_l,
                            offset_ldp |->  offset_ldp ] >>
                        \o stack
        /\ addr_ldp' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, ctx_, ctx >>

R215 == /\ pc = "R215"
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                        addr_ld, reg1_st, reg2_st, reg3_, offset_st, addr_st, 
                        reg1_ldp, reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                        reg2, reg3, offset, addr, ctx_, ctx >>

restore_context == R00 \/ R01 \/ R02 \/ R03 \/ R04 \/ R05 \/ R06 \/ R07
                      \/ R08 \/ R09 \/ R10 \/ R11 \/ R12 \/ R13 \/ R14
                      \/ R15 \/ R16 \/ R17 \/ R18 \/ R19 \/ R20 \/ R21
                      \/ R22 \/ R23 \/ R24 \/ R25 \/ R26 \/ R27 \/ R28
                      \/ R29 \/ R30 \/ R31 \/ R100 \/ R101 \/ R102 \/ R103
                      \/ R104 \/ R105 \/ R106 \/ R107 \/ R108 \/ R109
                      \/ R110 \/ R111 \/ R112 \/ R113 \/ R200 \/ R201
                      \/ R202 \/ R203 \/ R204 \/ R205 \/ R206 \/ R207
                      \/ R208 \/ R209 \/ R210 \/ R211 \/ R212 \/ R213
                      \/ R214 \/ R215

start_check_elr_null == /\ pc = "start_check_elr_null"
                        /\ Context' = init_context
                        /\ registers' = [registers EXCEPT !["x0"] = 0]
                        /\ pc' = "elr_null0"
                        /\ UNCHANGED << ctx_start, stack, reg1_, reg2_, 
                                        offset_, addr_, reg1_l, reg2_l, 
                                        offset_l, addr_l, reg1_s, reg2_s, 
                                        offset_s, addr_s, reg1_ld, reg2_ld, 
                                        offset_ld, addr_ld, reg1_st, reg2_st, 
                                        reg3_, offset_st, addr_st, reg1_ldp, 
                                        reg2_ldp, reg3_l, offset_ldp, addr_ldp, 
                                        reg1, reg2, reg3, offset, addr, ctx_, 
                                        ctx >>

elr_null0 == /\ pc = "elr_null0"
             /\ registers' = [registers EXCEPT !["elr"] = 0]
             /\ ctx_' = registers'
             /\ pc' = "elr_null1"
             /\ UNCHANGED << Context, ctx_start, stack, reg1_, reg2_, offset_, 
                             addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                             reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                             offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                             offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                             offset_ldp, addr_ldp, reg1, reg2, reg3, offset, 
                             addr, ctx >>

elr_null1 == /\ pc = "elr_null1"
             /\ stack' = << [ procedure |->  "save_context",
                              pc        |->  "elr_null2" ] >>
                          \o stack
             /\ pc' = "S00"
             /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, 
                             offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                             reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                             reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                             reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, 
                             reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                             offset, addr, ctx_, ctx >>

elr_null2 == /\ pc = "elr_null2"
             /\ registers' = [registers EXCEPT !["x0"] = 0]
             /\ stack' = << [ procedure |->  "restore_context",
                              pc        |->  "elr_null3" ] >>
                          \o stack
             /\ pc' = "R00"
             /\ UNCHANGED << Context, ctx_start, reg1_, reg2_, offset_, addr_, 
                             reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                             offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                             addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                             addr_st, reg1_ldp, reg2_ldp, reg3_l, offset_ldp, 
                             addr_ldp, reg1, reg2, reg3, offset, addr, ctx_, 
                             ctx >>

elr_null3 == /\ pc = "elr_null3"
             /\ Assert((registers = ctx_), 
                       "Failure of assertion at line 438, column 9.")
             /\ pc' = Head(stack).pc
             /\ ctx_' = Head(stack).ctx_
             /\ stack' = Tail(stack)
             /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, 
                             offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
                             reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                             reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                             reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, 
                             reg3_l, offset_ldp, addr_ldp, reg1, reg2, reg3, 
                             offset, addr, ctx >>

check_erl_null == start_check_elr_null \/ elr_null0 \/ elr_null1
                     \/ elr_null2 \/ elr_null3

start_elr_not_null == /\ pc = "start_elr_not_null"
                      /\ Context' = init_context
                      /\ registers' = [registers EXCEPT !["x0"] = 0]
                      /\ pc' = "elr_not_null0"
                      /\ UNCHANGED << ctx_start, stack, reg1_, reg2_, offset_, 
                                      addr_, reg1_l, reg2_l, offset_l, addr_l, 
                                      reg1_s, reg2_s, offset_s, addr_s, 
                                      reg1_ld, reg2_ld, offset_ld, addr_ld, 
                                      reg1_st, reg2_st, reg3_, offset_st, 
                                      addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                                      offset_ldp, addr_ldp, reg1, reg2, reg3, 
                                      offset, addr, ctx_, ctx >>

elr_not_null0 == /\ pc = "elr_not_null0"
                 /\ registers' = [registers EXCEPT !["elr"] = 200]
                 /\ Context' = [Context EXCEPT ![776] = 200]
                 /\ ctx_start' = registers'
                 /\ pc' = "elr_not_null1"
                 /\ UNCHANGED << stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                                 reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                                 offset_s, addr_s, reg1_ld, reg2_ld, offset_ld, 
                                 addr_ld, reg1_st, reg2_st, reg3_, offset_st, 
                                 addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                                 offset_ldp, addr_ldp, reg1, reg2, reg3, 
                                 offset, addr, ctx_, ctx >>

elr_not_null1 == /\ pc = "elr_not_null1"
                 /\ stack' = << [ procedure |->  "save_context",
                                  pc        |->  "elr_not_null2" ] >>
                              \o stack
                 /\ pc' = "S00"
                 /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, 
                                 offset_, addr_, reg1_l, reg2_l, offset_l, 
                                 addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                                 reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, 
                                 reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                                 reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                                 reg2, reg3, offset, addr, ctx_, ctx >>

elr_not_null2 == /\ pc = "elr_not_null2"
                 /\ registers' = [registers EXCEPT !["x0"] = 0]
                 /\ stack' = << [ procedure |->  "restore_context",
                                  pc        |->  "elr_not_null3" ] >>
                              \o stack
                 /\ pc' = "R00"
                 /\ UNCHANGED << Context, ctx_start, reg1_, reg2_, offset_, 
                                 addr_, reg1_l, reg2_l, offset_l, addr_l, 
                                 reg1_s, reg2_s, offset_s, addr_s, reg1_ld, 
                                 reg2_ld, offset_ld, addr_ld, reg1_st, reg2_st, 
                                 reg3_, offset_st, addr_st, reg1_ldp, reg2_ldp, 
                                 reg3_l, offset_ldp, addr_ldp, reg1, reg2, 
                                 reg3, offset, addr, ctx_, ctx >>

elr_not_null3 == /\ pc = "elr_not_null3"
                 /\ Assert((registers = ctx_start), 
                           "Failure of assertion at line 465, column 9.")
                 /\ pc' = Head(stack).pc
                 /\ ctx' = Head(stack).ctx
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, 
                                 offset_, addr_, reg1_l, reg2_l, offset_l, 
                                 addr_l, reg1_s, reg2_s, offset_s, addr_s, 
                                 reg1_ld, reg2_ld, offset_ld, addr_ld, reg1_st, 
                                 reg2_st, reg3_, offset_st, addr_st, reg1_ldp, 
                                 reg2_ldp, reg3_l, offset_ldp, addr_ldp, reg1, 
                                 reg2, reg3, offset, addr, ctx_ >>

check_elr_not_null == start_elr_not_null \/ elr_not_null0 \/ elr_not_null1
                         \/ elr_not_null2 \/ elr_not_null3

check1 == /\ pc = "check1"
          /\ stack' = << [ procedure |->  "check_erl_null",
                           pc        |->  "check2",
                           ctx_      |->  ctx_ ] >>
                       \o stack
          /\ ctx_' = defaultInitValue
          /\ pc' = "start_check_elr_null"
          /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                          addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                          reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                          offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                          offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                          offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                          ctx >>

check2 == /\ pc = "check2"
          /\ stack' = << [ procedure |->  "check_elr_not_null",
                           pc        |->  "Done",
                           ctx       |->  ctx ] >>
                       \o stack
          /\ ctx' = defaultInitValue
          /\ pc' = "start_elr_not_null"
          /\ UNCHANGED << Context, ctx_start, registers, reg1_, reg2_, offset_, 
                          addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                          reg2_s, offset_s, addr_s, reg1_ld, reg2_ld, 
                          offset_ld, addr_ld, reg1_st, reg2_st, reg3_, 
                          offset_st, addr_st, reg1_ldp, reg2_ldp, reg3_l, 
                          offset_ldp, addr_ldp, reg1, reg2, reg3, offset, addr, 
                          ctx_ >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == str \/ ldr \/ str_add \/ ldr_add \/ stp \/ ldp \/ ldp_add
           \/ save_context \/ restore_context \/ check_erl_null
           \/ check_elr_not_null \/ check1 \/ check2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
