----------------- MODULE callee_saved_regs ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT SIZE_CONTEXT

(*--algorithm callee_saved_regs

variables
    \* struct Context
    Context;

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
        d8 |-> 108,
        d9 |-> 109,
        d10 |-> 110,
        d11 |-> 111,
        d12 |-> 112,
        d13 |-> 113,
        d14 |-> 114,
        d15 |-> 115,

        \* system registers
        spsr |-> 202,
        fpsr |-> 203,
        fpcr |-> 204,

        \* stack pointer
        sp |-> 300
    ];

define
    CALLEE_SAVED == {
        "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "spsr", "fpsr", "fpcr", "sp"}

    init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
    calee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]
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
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
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
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
    ldr1:
        registers[reg1] := Context[addr];
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
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
    stp1:
        Context[addr] := registers[reg1];
    stp2:
        Context[addr + 8] := registers[reg2];
        return;
end procedure;

\* stp reg1, reg2, [reg3], offset
\*
\* [reg3 + offset] = reg1;
\* [reg3 + offset + 8] = reg2;
procedure stp_add(reg1, reg2, reg3, offset)
variables
    addr;
begin
    stp_add0:
        addr := registers[reg3];
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
    stp_add1:
        Context[addr] := registers[reg1];
    stp_add2:
        Context[addr + 8] := registers[reg2];
    stp_add3:
        registers[reg3] := addr + offset;
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
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
    ldp1:
        registers[reg1] := Context[addr];
    ldp2:
        registers[reg2] := Context[addr + 8];
        return;
end procedure;

\* ldp reg1, reg2, [reg3], offset
\*
\* reg1 = [reg3 + offset];
\* reg2 = [reg3 + offset + 8];
procedure ldp_add(reg1, reg2, reg3, offset)
variables
    addr;
begin
    ldp_add0:
        addr := registers[reg3];
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
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
    S00: call stp_add( "d8", "d9", "x0", 16);
    S01: call stp_add( "d10", "d11", "x0", 16);
    S02: call stp_add( "d12", "d13", "x0", 16);
    S03: call stp_add( "d14", "d15", "x0", 16);

    \* Store general purpose registers.
    S100: call stp("x19", "x20", "x0", 16 * 1);
    S101: call stp("x21", "x22", "x0", 16 * 2);
    S102: call stp("x23", "x24", "x0", 16 * 3);
    S103: call stp("x25", "x26", "x0", 16 * 4);
    S104: call stp("x27", "x28", "x0", 16 * 5);
    S105: call str("x30", "x0", 16 * 6);

    \* Store FPSR and FPCR registers.
    S200: msr("x9", "fpsr");
    S201: msr("x10", "fpcr");
    S202: call stp("x9", "x10", "x0", 0);

    \* Store SPSR.
    S203: add("x0", "x0", 16 * 7);
    S204: mrs("x11", "spsr");
    S205: call str("x11", "x0", 0);

    \* Store SP.
    S206: mov("x12", "sp");
    S207: call str("x12", "x0", -8);

    return;
end procedure;

procedure restore_context()
begin
    \* Load floating-point registers.
    R00: call ldp_add( "d8", "d9", "x0", 16);
    R01: call ldp_add( "d10", "d11", "x0", 16);
    R02: call ldp_add( "d12", "d13", "x0", 16);
    R03: call ldp_add( "d14", "d15", "x0", 16);

    \* Load general purpose registers.
    R100: call ldp("x19", "x20", "x0", 16 * 1);
    R101: call ldp("x21", "x22", "x0", 16 * 2);
    R102: call ldp("x23", "x24", "x0", 16 * 3);
    R103: call ldp("x25", "x26", "x0", 16 * 4);
    R104: call ldp("x27", "x28", "x0", 16 * 5);
    R114: call ldr("x30", "x0", 16 * 6);

    \* Load FPSR and FPCR registers.
    R200: call ldp("x9", "x10", "x0", 0);
    R201: msr("fpsr", "x9");
    R202: msr("fpcr", "x10");

    \* Load SPSR.
    R203: add("x0", "x0", 16 * 7);
    R204: call ldr("x11", "x0", 0);
    R205: msr("spsr", "x11");

    \* Load SP.
    R206: call ldr("x12", "x0", -8);
    R207: mov("sp", "x12");

    return;
end procedure;

procedure test()
variables
    start_ctx = calee_saved_registers;
begin
    start_test:
        Context := init_context;
        registers["x0"] := 0;

    call_save_context:
        call save_context();

    init_x0:
        registers["x0"] := 0;

    call_restore_context:
        call restore_context();

    end_test:
        assert(calee_saved_registers = start_ctx);

    return;
end procedure;

begin
    check1:
        call test();
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "65deb2f0" /\ chksum(tla) = "8fa770d3")
\* Procedure variable addr of procedure str at line 119 col 5 changed to addr_
\* Procedure variable addr of procedure ldr at line 134 col 5 changed to addr_l
\* Procedure variable addr of procedure stp at line 150 col 5 changed to addr_s
\* Procedure variable addr of procedure stp_add at line 168 col 5 changed to addr_st
\* Procedure variable addr of procedure ldp at line 188 col 5 changed to addr_ld
\* Parameter reg1 of procedure str at line 117 col 15 changed to reg1_
\* Parameter reg2 of procedure str at line 117 col 21 changed to reg2_
\* Parameter offset of procedure str at line 117 col 27 changed to offset_
\* Parameter reg1 of procedure ldr at line 132 col 15 changed to reg1_l
\* Parameter reg2 of procedure ldr at line 132 col 21 changed to reg2_l
\* Parameter offset of procedure ldr at line 132 col 27 changed to offset_l
\* Parameter reg1 of procedure stp at line 148 col 15 changed to reg1_s
\* Parameter reg2 of procedure stp at line 148 col 21 changed to reg2_s
\* Parameter reg3 of procedure stp at line 148 col 27 changed to reg3_
\* Parameter offset of procedure stp at line 148 col 33 changed to offset_s
\* Parameter reg1 of procedure stp_add at line 166 col 19 changed to reg1_st
\* Parameter reg2 of procedure stp_add at line 166 col 25 changed to reg2_st
\* Parameter reg3 of procedure stp_add at line 166 col 31 changed to reg3_s
\* Parameter offset of procedure stp_add at line 166 col 37 changed to offset_st
\* Parameter reg1 of procedure ldp at line 186 col 15 changed to reg1_ld
\* Parameter reg2 of procedure ldp at line 186 col 21 changed to reg2_ld
\* Parameter reg3 of procedure ldp at line 186 col 27 changed to reg3_l
\* Parameter offset of procedure ldp at line 186 col 33 changed to offset_ld
CONSTANT defaultInitValue
VARIABLES Context, registers, pc, stack

(* define statement *)
CALLEE_SAVED == {
    "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
    "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
    "spsr", "fpsr", "fpcr", "sp"}

init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
calee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]

VARIABLES reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
          reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
          offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
          reg1, reg2, reg3, offset, addr, start_ctx

vars == << Context, registers, pc, stack, reg1_, reg2_, offset_, addr_, 
           reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
           addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, reg1_ld, 
           reg2_ld, reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
           addr, start_ctx >>

Init == (* Global variables *)
        /\ Context = defaultInitValue
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
                       
                       
                           d8 |-> 108,
                           d9 |-> 109,
                           d10 |-> 110,
                           d11 |-> 111,
                           d12 |-> 112,
                           d13 |-> 113,
                           d14 |-> 114,
                           d15 |-> 115,
                       
                       
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
        (* Procedure ldp *)
        /\ reg1_ld = defaultInitValue
        /\ reg2_ld = defaultInitValue
        /\ reg3_l = defaultInitValue
        /\ offset_ld = defaultInitValue
        /\ addr_ld = defaultInitValue
        (* Procedure ldp_add *)
        /\ reg1 = defaultInitValue
        /\ reg2 = defaultInitValue
        /\ reg3 = defaultInitValue
        /\ offset = defaultInitValue
        /\ addr = defaultInitValue
        (* Procedure test *)
        /\ start_ctx = calee_saved_registers
        /\ stack = << >>
        /\ pc = "check1"

str0 == /\ pc = "str0"
        /\ addr_' = registers[reg2_] + offset_
        /\ Assert(0 <= addr_' /\ addr_' < SIZE_CONTEXT, 
                  "Failure of assertion at line 123, column 9.")
        /\ pc' = "str1"
        /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

str1 == /\ pc = "str1"
        /\ Context' = [Context EXCEPT ![addr_] = registers[reg1_]]
        /\ pc' = Head(stack).pc
        /\ addr_' = Head(stack).addr_
        /\ reg1_' = Head(stack).reg1_
        /\ reg2_' = Head(stack).reg2_
        /\ offset_' = Head(stack).offset_
        /\ stack' = Tail(stack)
        /\ UNCHANGED << registers, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

str == str0 \/ str1

ldr0 == /\ pc = "ldr0"
        /\ addr_l' = registers[reg2_l] + offset_l
        /\ Assert(0 <= addr_l' /\ addr_l' < SIZE_CONTEXT, 
                  "Failure of assertion at line 138, column 9.")
        /\ pc' = "ldr1"
        /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

ldr1 == /\ pc = "ldr1"
        /\ registers' = [registers EXCEPT ![reg1_l] = Context[addr_l]]
        /\ pc' = Head(stack).pc
        /\ addr_l' = Head(stack).addr_l
        /\ reg1_l' = Head(stack).reg1_l
        /\ reg2_l' = Head(stack).reg2_l
        /\ offset_l' = Head(stack).offset_l
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

ldr == ldr0 \/ ldr1

stp0 == /\ pc = "stp0"
        /\ addr_s' = registers[reg3_] + offset_s
        /\ Assert(0 <= addr_s' /\ addr_s' < SIZE_CONTEXT, 
                  "Failure of assertion at line 154, column 9.")
        /\ pc' = "stp1"
        /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

stp1 == /\ pc = "stp1"
        /\ Context' = [Context EXCEPT ![addr_s] = registers[reg1_s]]
        /\ pc' = "stp2"
        /\ UNCHANGED << registers, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

stp2 == /\ pc = "stp2"
        /\ Context' = [Context EXCEPT ![addr_s + 8] = registers[reg2_s]]
        /\ pc' = Head(stack).pc
        /\ addr_s' = Head(stack).addr_s
        /\ reg1_s' = Head(stack).reg1_s
        /\ reg2_s' = Head(stack).reg2_s
        /\ reg3_' = Head(stack).reg3_
        /\ offset_s' = Head(stack).offset_s
        /\ stack' = Tail(stack)
        /\ UNCHANGED << registers, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

stp == stp0 \/ stp1 \/ stp2

stp_add0 == /\ pc = "stp_add0"
            /\ addr_st' = registers[reg3_s]
            /\ Assert(0 <= addr_st' /\ addr_st' < SIZE_CONTEXT, 
                      "Failure of assertion at line 172, column 9.")
            /\ pc' = "stp_add1"
            /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                            reg3_s, offset_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            start_ctx >>

stp_add1 == /\ pc = "stp_add1"
            /\ Context' = [Context EXCEPT ![addr_st] = registers[reg1_st]]
            /\ pc' = "stp_add2"
            /\ UNCHANGED << registers, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                            offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            start_ctx >>

stp_add2 == /\ pc = "stp_add2"
            /\ Context' = [Context EXCEPT ![addr_st + 8] = registers[reg2_st]]
            /\ pc' = "stp_add3"
            /\ UNCHANGED << registers, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                            offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            start_ctx >>

stp_add3 == /\ pc = "stp_add3"
            /\ registers' = [registers EXCEPT ![reg3_s] = addr_st + offset_st]
            /\ pc' = Head(stack).pc
            /\ addr_st' = Head(stack).addr_st
            /\ reg1_st' = Head(stack).reg1_st
            /\ reg2_st' = Head(stack).reg2_st
            /\ reg3_s' = Head(stack).reg3_s
            /\ offset_st' = Head(stack).offset_st
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, 
                            reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                            offset_s, addr_s, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            start_ctx >>

stp_add == stp_add0 \/ stp_add1 \/ stp_add2 \/ stp_add3

ldp0 == /\ pc = "ldp0"
        /\ addr_ld' = registers[reg3_l] + offset_ld
        /\ Assert(0 <= addr_ld' /\ addr_ld' < SIZE_CONTEXT, 
                  "Failure of assertion at line 192, column 9.")
        /\ pc' = "ldp1"
        /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, reg1, reg2, reg3, offset, addr, start_ctx >>

ldp1 == /\ pc = "ldp1"
        /\ registers' = [registers EXCEPT ![reg1_ld] = Context[addr_ld]]
        /\ pc' = "ldp2"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

ldp2 == /\ pc = "ldp2"
        /\ registers' = [registers EXCEPT ![reg2_ld] = Context[addr_ld + 8]]
        /\ pc' = Head(stack).pc
        /\ addr_ld' = Head(stack).addr_ld
        /\ reg1_ld' = Head(stack).reg1_ld
        /\ reg2_ld' = Head(stack).reg2_ld
        /\ reg3_l' = Head(stack).reg3_l
        /\ offset_ld' = Head(stack).offset_ld
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

ldp == ldp0 \/ ldp1 \/ ldp2

ldp_add0 == /\ pc = "ldp_add0"
            /\ addr' = registers[reg3]
            /\ Assert(0 <= addr' /\ addr' < SIZE_CONTEXT, 
                      "Failure of assertion at line 210, column 9.")
            /\ pc' = "ldp_add1"
            /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, reg3_, offset_s, addr_s, reg1_st, reg2_st, 
                            reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                            reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, 
                            offset, start_ctx >>

ldp_add1 == /\ pc = "ldp_add1"
            /\ registers' = [registers EXCEPT ![reg1] = Context[addr]]
            /\ pc' = "ldp_add2"
            /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                            offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            start_ctx >>

ldp_add2 == /\ pc = "ldp_add2"
            /\ registers' = [registers EXCEPT ![reg2] = Context[addr + 8]]
            /\ pc' = "ldp_add3"
            /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                            offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                            start_ctx >>

ldp_add3 == /\ pc = "ldp_add3"
            /\ registers' = [registers EXCEPT ![reg3] = addr + offset]
            /\ pc' = Head(stack).pc
            /\ addr' = Head(stack).addr
            /\ reg1' = Head(stack).reg1
            /\ reg2' = Head(stack).reg2
            /\ reg3' = Head(stack).reg3
            /\ offset' = Head(stack).offset
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, 
                            reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                            offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                            offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, start_ctx >>

ldp_add == ldp_add0 \/ ldp_add1 \/ ldp_add2 \/ ldp_add3

S00 == /\ pc = "S00"
       /\ /\ offset_st' = 16
          /\ reg1_st' = "d8"
          /\ reg2_st' = "d9"
          /\ reg3_s' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S01",
                           addr_st   |->  addr_st,
                           reg1_st   |->  reg1_st,
                           reg2_st   |->  reg2_st,
                           reg3_s    |->  reg3_s,
                           offset_st |->  offset_st ] >>
                       \o stack
       /\ addr_st' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_ld, reg2_ld, reg3_l, offset_ld, 
                       addr_ld, reg1, reg2, reg3, offset, addr, start_ctx >>

S01 == /\ pc = "S01"
       /\ /\ offset_st' = 16
          /\ reg1_st' = "d10"
          /\ reg2_st' = "d11"
          /\ reg3_s' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S02",
                           addr_st   |->  addr_st,
                           reg1_st   |->  reg1_st,
                           reg2_st   |->  reg2_st,
                           reg3_s    |->  reg3_s,
                           offset_st |->  offset_st ] >>
                       \o stack
       /\ addr_st' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_ld, reg2_ld, reg3_l, offset_ld, 
                       addr_ld, reg1, reg2, reg3, offset, addr, start_ctx >>

S02 == /\ pc = "S02"
       /\ /\ offset_st' = 16
          /\ reg1_st' = "d12"
          /\ reg2_st' = "d13"
          /\ reg3_s' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S03",
                           addr_st   |->  addr_st,
                           reg1_st   |->  reg1_st,
                           reg2_st   |->  reg2_st,
                           reg3_s    |->  reg3_s,
                           offset_st |->  offset_st ] >>
                       \o stack
       /\ addr_st' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_ld, reg2_ld, reg3_l, offset_ld, 
                       addr_ld, reg1, reg2, reg3, offset, addr, start_ctx >>

S03 == /\ pc = "S03"
       /\ /\ offset_st' = 16
          /\ reg1_st' = "d14"
          /\ reg2_st' = "d15"
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
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_ld, reg2_ld, reg3_l, offset_ld, 
                       addr_ld, reg1, reg2, reg3, offset, addr, start_ctx >>

S100 == /\ pc = "S100"
        /\ /\ offset_s' = 16 * 1
           /\ reg1_s' = "x19"
           /\ reg2_s' = "x20"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S101",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S101 == /\ pc = "S101"
        /\ /\ offset_s' = 16 * 2
           /\ reg1_s' = "x21"
           /\ reg2_s' = "x22"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S102",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S102 == /\ pc = "S102"
        /\ /\ offset_s' = 16 * 3
           /\ reg1_s' = "x23"
           /\ reg2_s' = "x24"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S103",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S103 == /\ pc = "S103"
        /\ /\ offset_s' = 16 * 4
           /\ reg1_s' = "x25"
           /\ reg2_s' = "x26"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S104",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S104 == /\ pc = "S104"
        /\ /\ offset_s' = 16 * 5
           /\ reg1_s' = "x27"
           /\ reg2_s' = "x28"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S105",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S105 == /\ pc = "S105"
        /\ /\ offset_' = 16 * 6
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
        /\ UNCHANGED << Context, registers, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

S200 == /\ pc = "S200"
        /\ registers' = [registers EXCEPT !["x9"] = registers["fpsr"]]
        /\ pc' = "S201"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

S201 == /\ pc = "S201"
        /\ registers' = [registers EXCEPT !["x10"] = registers["fpcr"]]
        /\ pc' = "S202"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

S202 == /\ pc = "S202"
        /\ /\ offset_s' = 0
           /\ reg1_s' = "x9"
           /\ reg2_s' = "x10"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp",
                            pc        |->  "S203",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_st, reg2_st, 
                        reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                        offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S203 == /\ pc = "S203"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] + (16 * 7)]
        /\ pc' = "S204"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

S204 == /\ pc = "S204"
        /\ registers' = [registers EXCEPT !["x11"] = registers["spsr"]]
        /\ pc' = "S205"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

S205 == /\ pc = "S205"
        /\ /\ offset_' = 0
           /\ reg1_' = "x11"
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
        /\ UNCHANGED << Context, registers, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

S206 == /\ pc = "S206"
        /\ registers' = [registers EXCEPT !["x12"] = registers["sp"]]
        /\ pc' = "S207"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

S207 == /\ pc = "S207"
        /\ /\ offset_' = -8
           /\ reg1_' = "x12"
           /\ reg2_' = "x0"
           /\ stack' = << [ procedure |->  "str",
                            pc        |->  Head(stack).pc,
                            addr_     |->  addr_,
                            reg1_     |->  reg1_,
                            reg2_     |->  reg2_,
                            offset_   |->  offset_ ] >>
                        \o Tail(stack)
        /\ addr_' = defaultInitValue
        /\ pc' = "str0"
        /\ UNCHANGED << Context, registers, reg1_l, reg2_l, offset_l, addr_l, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

save_context == S00 \/ S01 \/ S02 \/ S03 \/ S100 \/ S101 \/ S102 \/ S103
                   \/ S104 \/ S105 \/ S200 \/ S201 \/ S202 \/ S203 \/ S204
                   \/ S205 \/ S206 \/ S207

R00 == /\ pc = "R00"
       /\ /\ offset' = 16
          /\ reg1' = "d8"
          /\ reg2' = "d9"
          /\ reg3' = "x0"
          /\ stack' = << [ procedure |->  "ldp_add",
                           pc        |->  "R01",
                           addr      |->  addr,
                           reg1      |->  reg1,
                           reg2      |->  reg2,
                           reg3      |->  reg3,
                           offset    |->  offset ] >>
                       \o stack
       /\ addr' = defaultInitValue
       /\ pc' = "ldp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                       addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                       start_ctx >>

R01 == /\ pc = "R01"
       /\ /\ offset' = 16
          /\ reg1' = "d10"
          /\ reg2' = "d11"
          /\ reg3' = "x0"
          /\ stack' = << [ procedure |->  "ldp_add",
                           pc        |->  "R02",
                           addr      |->  addr,
                           reg1      |->  reg1,
                           reg2      |->  reg2,
                           reg3      |->  reg3,
                           offset    |->  offset ] >>
                       \o stack
       /\ addr' = defaultInitValue
       /\ pc' = "ldp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                       addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                       start_ctx >>

R02 == /\ pc = "R02"
       /\ /\ offset' = 16
          /\ reg1' = "d12"
          /\ reg2' = "d13"
          /\ reg3' = "x0"
          /\ stack' = << [ procedure |->  "ldp_add",
                           pc        |->  "R03",
                           addr      |->  addr,
                           reg1      |->  reg1,
                           reg2      |->  reg2,
                           reg3      |->  reg3,
                           offset    |->  offset ] >>
                       \o stack
       /\ addr' = defaultInitValue
       /\ pc' = "ldp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                       addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                       start_ctx >>

R03 == /\ pc = "R03"
       /\ /\ offset' = 16
          /\ reg1' = "d14"
          /\ reg2' = "d15"
          /\ reg3' = "x0"
          /\ stack' = << [ procedure |->  "ldp_add",
                           pc        |->  "R100",
                           addr      |->  addr,
                           reg1      |->  reg1,
                           reg2      |->  reg2,
                           reg3      |->  reg3,
                           offset    |->  offset ] >>
                       \o stack
       /\ addr' = defaultInitValue
       /\ pc' = "ldp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                       offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                       addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                       start_ctx >>

R100 == /\ pc = "R100"
        /\ /\ offset_ld' = 16 * 1
           /\ reg1_ld' = "x19"
           /\ reg2_ld' = "x20"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R101",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

R101 == /\ pc = "R101"
        /\ /\ offset_ld' = 16 * 2
           /\ reg1_ld' = "x21"
           /\ reg2_ld' = "x22"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R102",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

R102 == /\ pc = "R102"
        /\ /\ offset_ld' = 16 * 3
           /\ reg1_ld' = "x23"
           /\ reg2_ld' = "x24"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R103",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

R103 == /\ pc = "R103"
        /\ /\ offset_ld' = 16 * 4
           /\ reg1_ld' = "x25"
           /\ reg2_ld' = "x26"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R104",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

R104 == /\ pc = "R104"
        /\ /\ offset_ld' = 16 * 5
           /\ reg1_ld' = "x27"
           /\ reg2_ld' = "x28"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R114",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

R114 == /\ pc = "R114"
        /\ /\ offset_l' = 16 * 6
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
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

R200 == /\ pc = "R200"
        /\ /\ offset_ld' = 0
           /\ reg1_ld' = "x9"
           /\ reg2_ld' = "x10"
           /\ reg3_l' = "x0"
           /\ stack' = << [ procedure |->  "ldp",
                            pc        |->  "R201",
                            addr_ld   |->  addr_ld,
                            reg1_ld   |->  reg1_ld,
                            reg2_ld   |->  reg2_ld,
                            reg3_l    |->  reg3_l,
                            offset_ld |->  offset_ld ] >>
                        \o stack
        /\ addr_ld' = defaultInitValue
        /\ pc' = "ldp0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                        offset_st, addr_st, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

R201 == /\ pc = "R201"
        /\ registers' = [registers EXCEPT !["fpsr"] = registers["x9"]]
        /\ pc' = "R202"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

R202 == /\ pc = "R202"
        /\ registers' = [registers EXCEPT !["fpcr"] = registers["x10"]]
        /\ pc' = "R203"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

R203 == /\ pc = "R203"
        /\ registers' = [registers EXCEPT !["x0"] = registers["x0"] + (16 * 7)]
        /\ pc' = "R204"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

R204 == /\ pc = "R204"
        /\ /\ offset_l' = 0
           /\ reg1_l' = "x11"
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
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

R205 == /\ pc = "R205"
        /\ registers' = [registers EXCEPT !["spsr"] = registers["x11"]]
        /\ pc' = "R206"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1_st, reg2_st, reg3_s, offset_st, 
                        addr_st, reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, 
                        reg1, reg2, reg3, offset, addr, start_ctx >>

R206 == /\ pc = "R206"
        /\ /\ offset_l' = -8
           /\ reg1_l' = "x12"
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
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1_st, 
                        reg2_st, reg3_s, offset_st, addr_st, reg1_ld, reg2_ld, 
                        reg3_l, offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

R207 == /\ pc = "R207"
        /\ registers' = [registers EXCEPT !["sp"] = registers["x12"]]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1_st, reg2_st, reg3_s, offset_st, addr_st, 
                        reg1_ld, reg2_ld, reg3_l, offset_ld, addr_ld, reg1, 
                        reg2, reg3, offset, addr, start_ctx >>

restore_context == R00 \/ R01 \/ R02 \/ R03 \/ R100 \/ R101 \/ R102 \/ R103
                      \/ R104 \/ R114 \/ R200 \/ R201 \/ R202 \/ R203
                      \/ R204 \/ R205 \/ R206 \/ R207

start_test == /\ pc = "start_test"
              /\ Context' = init_context
              /\ registers' = [registers EXCEPT !["x0"] = 0]
              /\ pc' = "call_save_context"
              /\ UNCHANGED << stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                              reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                              offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                              offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                              offset_ld, addr_ld, reg1, reg2, reg3, offset, 
                              addr, start_ctx >>

call_save_context == /\ pc = "call_save_context"
                     /\ stack' = << [ procedure |->  "save_context",
                                      pc        |->  "init_x0" ] >>
                                  \o stack
                     /\ pc' = "S00"
                     /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, 
                                     addr_, reg1_l, reg2_l, offset_l, addr_l, 
                                     reg1_s, reg2_s, reg3_, offset_s, addr_s, 
                                     reg1_st, reg2_st, reg3_s, offset_st, 
                                     addr_st, reg1_ld, reg2_ld, reg3_l, 
                                     offset_ld, addr_ld, reg1, reg2, reg3, 
                                     offset, addr, start_ctx >>

init_x0 == /\ pc = "init_x0"
           /\ registers' = [registers EXCEPT !["x0"] = 0]
           /\ pc' = "call_restore_context"
           /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, 
                           reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                           reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                           offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                           offset_ld, addr_ld, reg1, reg2, reg3, offset, addr, 
                           start_ctx >>

call_restore_context == /\ pc = "call_restore_context"
                        /\ stack' = << [ procedure |->  "restore_context",
                                         pc        |->  "end_test" ] >>
                                     \o stack
                        /\ pc' = "R00"
                        /\ UNCHANGED << Context, registers, reg1_, reg2_, 
                                        offset_, addr_, reg1_l, reg2_l, 
                                        offset_l, addr_l, reg1_s, reg2_s, 
                                        reg3_, offset_s, addr_s, reg1_st, 
                                        reg2_st, reg3_s, offset_st, addr_st, 
                                        reg1_ld, reg2_ld, reg3_l, offset_ld, 
                                        addr_ld, reg1, reg2, reg3, offset, 
                                        addr, start_ctx >>

end_test == /\ pc = "end_test"
            /\ Assert((calee_saved_registers = start_ctx), 
                      "Failure of assertion at line 304, column 9.")
            /\ pc' = Head(stack).pc
            /\ start_ctx' = Head(stack).start_ctx
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                            offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                            offset_ld, addr_ld, reg1, reg2, reg3, offset, addr >>

test == start_test \/ call_save_context \/ init_x0 \/ call_restore_context
           \/ end_test

check1 == /\ pc = "check1"
          /\ stack' = << [ procedure |->  "test",
                           pc        |->  "Done",
                           start_ctx |->  start_ctx ] >>
                       \o stack
          /\ start_ctx' = calee_saved_registers
          /\ pc' = "start_test"
          /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                          reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                          reg3_, offset_s, addr_s, reg1_st, reg2_st, reg3_s, 
                          offset_st, addr_st, reg1_ld, reg2_ld, reg3_l, 
                          offset_ld, addr_ld, reg1, reg2, reg3, offset, addr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == str \/ ldr \/ stp \/ stp_add \/ ldp \/ ldp_add \/ save_context
           \/ restore_context \/ test \/ check1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
