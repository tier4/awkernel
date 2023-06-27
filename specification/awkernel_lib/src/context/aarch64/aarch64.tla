----------------- MODULE aarch64 ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT SIZE_CONTEXT

(*--algorithm aarch64

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

        \* stack pointer
        sp |-> 300
    ];

define
    CALLEE_SAVED == {
        "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "sp"}

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
    S00: call stp_add(  "d8",  "d9", "x0", 16);
    S01: call stp_add( "d10", "d11", "x0", 16);
    S02: call stp_add( "d12", "d13", "x0", 16);
    S03: call stp_add( "d14", "d15", "x0", 16);

    \* Store general purpose registers.
    S100: call stp_add("x19", "x20", "x0", 16);
    S101: call stp_add("x21", "x22", "x0", 16);
    S102: call stp_add("x23", "x24", "x0", 16);
    S103: call stp_add("x25", "x26", "x0", 16);
    S104: call stp_add("x27", "x28", "x0", 16);
    S105: call stp_add("x29", "x30", "x0", 16);

    \* Store SP.
    S206: mov("x9", "sp");
    S207: call str("x9", "x0", 0);

    return;
end procedure;

procedure restore_context()
begin
    \* Load floating-point registers.
    R00: call ldp_add(  "d8",  "d9", "x1", 16);
    R01: call ldp_add( "d10", "d11", "x1", 16);
    R02: call ldp_add( "d12", "d13", "x1", 16);
    R03: call ldp_add( "d14", "d15", "x1", 16);

    \* Load general purpose registers.
    R100: call ldp_add("x19", "x20", "x1", 16);
    R101: call ldp_add("x21", "x22", "x1", 16);
    R102: call ldp_add("x23", "x24", "x1", 16);
    R103: call ldp_add("x25", "x26", "x1", 16);
    R104: call ldp_add("x27", "x28", "x1", 16);
    R105: call ldp_add("x29", "x30", "x1", 16);

    \* Load SP.
    R206: call ldr("x9", "x0", 0);
    R207: mov("sp", "x9");

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

    call_update:
        call update();

    init_x0:
        registers["x1"] := 0;

    call_restore_context:
        call restore_context();

    end_test:
        assert(calee_saved_registers = start_ctx);

    return;
end procedure;


procedure update() begin
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

    H108: inc("d8");
    H109: inc("d9");
    H110: inc("d10");
    H111: inc("d11");
    H112: inc("d12");
    H113: inc("d13");
    H114: inc("d14");
    H115: inc("d15");

    return;
end procedure;

begin
    check1:
        call test();
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "4d2bfff4" /\ chksum(tla) = "3306c342")
\* Procedure variable addr of procedure str at line 114 col 5 changed to addr_
\* Procedure variable addr of procedure ldr at line 129 col 5 changed to addr_l
\* Procedure variable addr of procedure stp_add at line 145 col 5 changed to addr_s
\* Parameter reg1 of procedure str at line 112 col 15 changed to reg1_
\* Parameter reg2 of procedure str at line 112 col 21 changed to reg2_
\* Parameter offset of procedure str at line 112 col 27 changed to offset_
\* Parameter reg1 of procedure ldr at line 127 col 15 changed to reg1_l
\* Parameter reg2 of procedure ldr at line 127 col 21 changed to reg2_l
\* Parameter offset of procedure ldr at line 127 col 27 changed to offset_l
\* Parameter reg1 of procedure stp_add at line 143 col 19 changed to reg1_s
\* Parameter reg2 of procedure stp_add at line 143 col 25 changed to reg2_s
\* Parameter reg3 of procedure stp_add at line 143 col 31 changed to reg3_
\* Parameter offset of procedure stp_add at line 143 col 37 changed to offset_s
CONSTANT defaultInitValue
VARIABLES Context, registers, pc, stack

(* define statement *)
CALLEE_SAVED == {
    "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30",
    "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
    "sp"}

init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
calee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]

VARIABLES reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, offset_l, addr_l, 
          reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
          addr, start_ctx

vars == << Context, registers, pc, stack, reg1_, reg2_, offset_, addr_, 
           reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
           addr_s, reg1, reg2, reg3, offset, addr, start_ctx >>

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
        (* Procedure stp_add *)
        /\ reg1_s = defaultInitValue
        /\ reg2_s = defaultInitValue
        /\ reg3_ = defaultInitValue
        /\ offset_s = defaultInitValue
        /\ addr_s = defaultInitValue
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
                  "Failure of assertion at line 118, column 9.")
        /\ pc' = "str1"
        /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

str1 == /\ pc = "str1"
        /\ Context' = [Context EXCEPT ![addr_] = registers[reg1_]]
        /\ pc' = Head(stack).pc
        /\ addr_' = Head(stack).addr_
        /\ reg1_' = Head(stack).reg1_
        /\ reg2_' = Head(stack).reg2_
        /\ offset_' = Head(stack).offset_
        /\ stack' = Tail(stack)
        /\ UNCHANGED << registers, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                        reg2_s, reg3_, offset_s, addr_s, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

str == str0 \/ str1

ldr0 == /\ pc = "ldr0"
        /\ addr_l' = registers[reg2_l] + offset_l
        /\ Assert(0 <= addr_l' /\ addr_l' < SIZE_CONTEXT, 
                  "Failure of assertion at line 133, column 9.")
        /\ pc' = "ldr1"
        /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                        addr_, reg1_l, reg2_l, offset_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

ldr1 == /\ pc = "ldr1"
        /\ registers' = [registers EXCEPT ![reg1_l] = Context[addr_l]]
        /\ pc' = Head(stack).pc
        /\ addr_l' = Head(stack).addr_l
        /\ reg1_l' = Head(stack).reg1_l
        /\ reg2_l' = Head(stack).reg2_l
        /\ offset_l' = Head(stack).offset_l
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                        addr, start_ctx >>

ldr == ldr0 \/ ldr1

stp_add0 == /\ pc = "stp_add0"
            /\ addr_s' = registers[reg3_]
            /\ Assert(0 <= addr_s' /\ addr_s' < SIZE_CONTEXT, 
                      "Failure of assertion at line 149, column 9.")
            /\ pc' = "stp_add1"
            /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, reg3_, offset_s, reg1, reg2, reg3, offset, 
                            addr, start_ctx >>

stp_add1 == /\ pc = "stp_add1"
            /\ Context' = [Context EXCEPT ![addr_s] = registers[reg1_s]]
            /\ pc' = "stp_add2"
            /\ UNCHANGED << registers, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                            addr, start_ctx >>

stp_add2 == /\ pc = "stp_add2"
            /\ Context' = [Context EXCEPT ![addr_s + 8] = registers[reg2_s]]
            /\ pc' = "stp_add3"
            /\ UNCHANGED << registers, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                            addr, start_ctx >>

stp_add3 == /\ pc = "stp_add3"
            /\ registers' = [registers EXCEPT ![reg3_] = addr_s + offset_s]
            /\ pc' = Head(stack).pc
            /\ addr_s' = Head(stack).addr_s
            /\ reg1_s' = Head(stack).reg1_s
            /\ reg2_s' = Head(stack).reg2_s
            /\ reg3_' = Head(stack).reg3_
            /\ offset_s' = Head(stack).offset_s
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, 
                            reg2_l, offset_l, addr_l, reg1, reg2, reg3, offset, 
                            addr, start_ctx >>

stp_add == stp_add0 \/ stp_add1 \/ stp_add2 \/ stp_add3

ldp_add0 == /\ pc = "ldp_add0"
            /\ addr' = registers[reg3]
            /\ Assert(0 <= addr' /\ addr' < SIZE_CONTEXT, 
                      "Failure of assertion at line 169, column 9.")
            /\ pc' = "ldp_add1"
            /\ UNCHANGED << Context, registers, stack, reg1_, reg2_, offset_, 
                            addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                            reg2_s, reg3_, offset_s, addr_s, reg1, reg2, reg3, 
                            offset, start_ctx >>

ldp_add1 == /\ pc = "ldp_add1"
            /\ registers' = [registers EXCEPT ![reg1] = Context[addr]]
            /\ pc' = "ldp_add2"
            /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                            addr, start_ctx >>

ldp_add2 == /\ pc = "ldp_add2"
            /\ registers' = [registers EXCEPT ![reg2] = Context[addr + 8]]
            /\ pc' = "ldp_add3"
            /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                            addr, start_ctx >>

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
                            offset_s, addr_s, start_ctx >>

ldp_add == ldp_add0 \/ ldp_add1 \/ ldp_add2 \/ ldp_add3

S00 == /\ pc = "S00"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "d8"
          /\ reg2_s' = "d9"
          /\ reg3_' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S01",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           reg3_     |->  reg3_,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                       offset, addr, start_ctx >>

S01 == /\ pc = "S01"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "d10"
          /\ reg2_s' = "d11"
          /\ reg3_' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S02",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           reg3_     |->  reg3_,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                       offset, addr, start_ctx >>

S02 == /\ pc = "S02"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "d12"
          /\ reg2_s' = "d13"
          /\ reg3_' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S03",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           reg3_     |->  reg3_,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                       offset, addr, start_ctx >>

S03 == /\ pc = "S03"
       /\ /\ offset_s' = 16
          /\ reg1_s' = "d14"
          /\ reg2_s' = "d15"
          /\ reg3_' = "x0"
          /\ stack' = << [ procedure |->  "stp_add",
                           pc        |->  "S100",
                           addr_s    |->  addr_s,
                           reg1_s    |->  reg1_s,
                           reg2_s    |->  reg2_s,
                           reg3_     |->  reg3_,
                           offset_s  |->  offset_s ] >>
                       \o stack
       /\ addr_s' = defaultInitValue
       /\ pc' = "stp_add0"
       /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                       reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                       offset, addr, start_ctx >>

S100 == /\ pc = "S100"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x19"
           /\ reg2_s' = "x20"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S101",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

S101 == /\ pc = "S101"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x21"
           /\ reg2_s' = "x22"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S102",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

S102 == /\ pc = "S102"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x23"
           /\ reg2_s' = "x24"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S103",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

S103 == /\ pc = "S103"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x25"
           /\ reg2_s' = "x26"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S104",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

S104 == /\ pc = "S104"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x27"
           /\ reg2_s' = "x28"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S105",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

S105 == /\ pc = "S105"
        /\ /\ offset_s' = 16
           /\ reg1_s' = "x29"
           /\ reg2_s' = "x30"
           /\ reg3_' = "x0"
           /\ stack' = << [ procedure |->  "stp_add",
                            pc        |->  "S206",
                            addr_s    |->  addr_s,
                            reg1_s    |->  reg1_s,
                            reg2_s    |->  reg2_s,
                            reg3_     |->  reg3_,
                            offset_s  |->  offset_s ] >>
                        \o stack
        /\ addr_s' = defaultInitValue
        /\ pc' = "stp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1, reg2, reg3, 
                        offset, addr, start_ctx >>

S206 == /\ pc = "S206"
        /\ registers' = [registers EXCEPT !["x9"] = registers["sp"]]
        /\ pc' = "S207"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

S207 == /\ pc = "S207"
        /\ /\ offset_' = 0
           /\ reg1_' = "x9"
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1, reg2, 
                        reg3, offset, addr, start_ctx >>

save_context == S00 \/ S01 \/ S02 \/ S03 \/ S100 \/ S101 \/ S102 \/ S103
                   \/ S104 \/ S105 \/ S206 \/ S207

R00 == /\ pc = "R00"
       /\ /\ offset' = 16
          /\ reg1' = "d8"
          /\ reg2' = "d9"
          /\ reg3' = "x1"
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
                       offset_s, addr_s, start_ctx >>

R01 == /\ pc = "R01"
       /\ /\ offset' = 16
          /\ reg1' = "d10"
          /\ reg2' = "d11"
          /\ reg3' = "x1"
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
                       offset_s, addr_s, start_ctx >>

R02 == /\ pc = "R02"
       /\ /\ offset' = 16
          /\ reg1' = "d12"
          /\ reg2' = "d13"
          /\ reg3' = "x1"
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
                       offset_s, addr_s, start_ctx >>

R03 == /\ pc = "R03"
       /\ /\ offset' = 16
          /\ reg1' = "d14"
          /\ reg2' = "d15"
          /\ reg3' = "x1"
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
                       offset_s, addr_s, start_ctx >>

R100 == /\ pc = "R100"
        /\ /\ offset' = 16
           /\ reg1' = "x19"
           /\ reg2' = "x20"
           /\ reg3' = "x1"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R101",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, start_ctx >>

R101 == /\ pc = "R101"
        /\ /\ offset' = 16
           /\ reg1' = "x21"
           /\ reg2' = "x22"
           /\ reg3' = "x1"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R102",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, start_ctx >>

R102 == /\ pc = "R102"
        /\ /\ offset' = 16
           /\ reg1' = "x23"
           /\ reg2' = "x24"
           /\ reg3' = "x1"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R103",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, start_ctx >>

R103 == /\ pc = "R103"
        /\ /\ offset' = 16
           /\ reg1' = "x25"
           /\ reg2' = "x26"
           /\ reg3' = "x1"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R104",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, start_ctx >>

R104 == /\ pc = "R104"
        /\ /\ offset' = 16
           /\ reg1' = "x27"
           /\ reg2' = "x28"
           /\ reg3' = "x1"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R105",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, start_ctx >>

R105 == /\ pc = "R105"
        /\ /\ offset' = 16
           /\ reg1' = "x29"
           /\ reg2' = "x30"
           /\ reg3' = "x1"
           /\ stack' = << [ procedure |->  "ldp_add",
                            pc        |->  "R206",
                            addr      |->  addr,
                            reg1      |->  reg1,
                            reg2      |->  reg2,
                            reg3      |->  reg3,
                            offset    |->  offset ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "ldp_add0"
        /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                        reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                        reg3_, offset_s, addr_s, start_ctx >>

R206 == /\ pc = "R206"
        /\ /\ offset_l' = 0
           /\ reg1_l' = "x9"
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
                        reg1_s, reg2_s, reg3_, offset_s, addr_s, reg1, reg2, 
                        reg3, offset, addr, start_ctx >>

R207 == /\ pc = "R207"
        /\ registers' = [registers EXCEPT !["sp"] = registers["x9"]]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1, reg2, reg3, offset, addr, start_ctx >>

restore_context == R00 \/ R01 \/ R02 \/ R03 \/ R100 \/ R101 \/ R102 \/ R103
                      \/ R104 \/ R105 \/ R206 \/ R207

start_test == /\ pc = "start_test"
              /\ Context' = init_context
              /\ registers' = [registers EXCEPT !["x0"] = 0]
              /\ pc' = "call_save_context"
              /\ UNCHANGED << stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                              reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                              offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                              start_ctx >>

call_save_context == /\ pc = "call_save_context"
                     /\ stack' = << [ procedure |->  "save_context",
                                      pc        |->  "call_update" ] >>
                                  \o stack
                     /\ pc' = "S00"
                     /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, 
                                     addr_, reg1_l, reg2_l, offset_l, addr_l, 
                                     reg1_s, reg2_s, reg3_, offset_s, addr_s, 
                                     reg1, reg2, reg3, offset, addr, start_ctx >>

call_update == /\ pc = "call_update"
               /\ stack' = << [ procedure |->  "update",
                                pc        |->  "init_x0" ] >>
                            \o stack
               /\ pc' = "H019"
               /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, 
                               addr_, reg1_l, reg2_l, offset_l, addr_l, reg1_s, 
                               reg2_s, reg3_, offset_s, addr_s, reg1, reg2, 
                               reg3, offset, addr, start_ctx >>

init_x0 == /\ pc = "init_x0"
           /\ registers' = [registers EXCEPT !["x1"] = 0]
           /\ pc' = "call_restore_context"
           /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, 
                           reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                           reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                           addr, start_ctx >>

call_restore_context == /\ pc = "call_restore_context"
                        /\ stack' = << [ procedure |->  "restore_context",
                                         pc        |->  "end_test" ] >>
                                     \o stack
                        /\ pc' = "R00"
                        /\ UNCHANGED << Context, registers, reg1_, reg2_, 
                                        offset_, addr_, reg1_l, reg2_l, 
                                        offset_l, addr_l, reg1_s, reg2_s, 
                                        reg3_, offset_s, addr_s, reg1, reg2, 
                                        reg3, offset, addr, start_ctx >>

end_test == /\ pc = "end_test"
            /\ Assert((calee_saved_registers = start_ctx), 
                      "Failure of assertion at line 246, column 9.")
            /\ pc' = Head(stack).pc
            /\ start_ctx' = Head(stack).start_ctx
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                            reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                            reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                            addr >>

test == start_test \/ call_save_context \/ call_update \/ init_x0
           \/ call_restore_context \/ end_test

H019 == /\ pc = "H019"
        /\ registers' = [registers EXCEPT !["x19"] = registers["x19"] + 1]
        /\ pc' = "H020"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H020 == /\ pc = "H020"
        /\ registers' = [registers EXCEPT !["x20"] = registers["x20"] + 1]
        /\ pc' = "H021"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H021 == /\ pc = "H021"
        /\ registers' = [registers EXCEPT !["x21"] = registers["x21"] + 1]
        /\ pc' = "H022"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H022 == /\ pc = "H022"
        /\ registers' = [registers EXCEPT !["x22"] = registers["x22"] + 1]
        /\ pc' = "H023"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H023 == /\ pc = "H023"
        /\ registers' = [registers EXCEPT !["x23"] = registers["x23"] + 1]
        /\ pc' = "H024"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H024 == /\ pc = "H024"
        /\ registers' = [registers EXCEPT !["x24"] = registers["x24"] + 1]
        /\ pc' = "H025"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H025 == /\ pc = "H025"
        /\ registers' = [registers EXCEPT !["x25"] = registers["x25"] + 1]
        /\ pc' = "H026"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H026 == /\ pc = "H026"
        /\ registers' = [registers EXCEPT !["x26"] = registers["x26"] + 1]
        /\ pc' = "H027"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H027 == /\ pc = "H027"
        /\ registers' = [registers EXCEPT !["x27"] = registers["x27"] + 1]
        /\ pc' = "H028"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H028 == /\ pc = "H028"
        /\ registers' = [registers EXCEPT !["x28"] = registers["x28"] + 1]
        /\ pc' = "H029"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H029 == /\ pc = "H029"
        /\ registers' = [registers EXCEPT !["x29"] = registers["x29"] + 1]
        /\ pc' = "H030"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H030 == /\ pc = "H030"
        /\ registers' = [registers EXCEPT !["x30"] = registers["x30"] + 1]
        /\ pc' = "H108"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H108 == /\ pc = "H108"
        /\ registers' = [registers EXCEPT !["d8"] = registers["d8"] + 1]
        /\ pc' = "H109"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H109 == /\ pc = "H109"
        /\ registers' = [registers EXCEPT !["d9"] = registers["d9"] + 1]
        /\ pc' = "H110"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H110 == /\ pc = "H110"
        /\ registers' = [registers EXCEPT !["d10"] = registers["d10"] + 1]
        /\ pc' = "H111"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H111 == /\ pc = "H111"
        /\ registers' = [registers EXCEPT !["d11"] = registers["d11"] + 1]
        /\ pc' = "H112"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H112 == /\ pc = "H112"
        /\ registers' = [registers EXCEPT !["d12"] = registers["d12"] + 1]
        /\ pc' = "H113"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H113 == /\ pc = "H113"
        /\ registers' = [registers EXCEPT !["d13"] = registers["d13"] + 1]
        /\ pc' = "H114"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H114 == /\ pc = "H114"
        /\ registers' = [registers EXCEPT !["d14"] = registers["d14"] + 1]
        /\ pc' = "H115"
        /\ UNCHANGED << Context, stack, reg1_, reg2_, offset_, addr_, reg1_l, 
                        reg2_l, offset_l, addr_l, reg1_s, reg2_s, reg3_, 
                        offset_s, addr_s, reg1, reg2, reg3, offset, addr, 
                        start_ctx >>

H115 == /\ pc = "H115"
        /\ registers' = [registers EXCEPT !["d15"] = registers["d15"] + 1]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg1_, reg2_, offset_, addr_, reg1_l, reg2_l, 
                        offset_l, addr_l, reg1_s, reg2_s, reg3_, offset_s, 
                        addr_s, reg1, reg2, reg3, offset, addr, start_ctx >>

update == H019 \/ H020 \/ H021 \/ H022 \/ H023 \/ H024 \/ H025 \/ H026
             \/ H027 \/ H028 \/ H029 \/ H030 \/ H108 \/ H109 \/ H110
             \/ H111 \/ H112 \/ H113 \/ H114 \/ H115

check1 == /\ pc = "check1"
          /\ stack' = << [ procedure |->  "test",
                           pc        |->  "Done",
                           start_ctx |->  start_ctx ] >>
                       \o stack
          /\ start_ctx' = calee_saved_registers
          /\ pc' = "start_test"
          /\ UNCHANGED << Context, registers, reg1_, reg2_, offset_, addr_, 
                          reg1_l, reg2_l, offset_l, addr_l, reg1_s, reg2_s, 
                          reg3_, offset_s, addr_s, reg1, reg2, reg3, offset, 
                          addr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == str \/ ldr \/ stp_add \/ ldp_add \/ save_context \/ restore_context
           \/ test \/ update \/ check1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
