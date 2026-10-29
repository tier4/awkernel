----------------- MODULE rv64 ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT SIZE_CONTEXT

(*--algorithm rv64

variables
    Context;

    registers = [
        \* general purpose registers
        ra  |-> 1,    \* return address
        sp  |-> 2,    \* stack pointer
        gp  |-> 3,
        tp  |-> 4,
        t0  |-> 5,
        t1  |-> 6,
        t2  |-> 7,
        s0  |-> 8,    \* frame pointer
        s1  |-> 9,
        a0  |-> 0,    \* used to pass 1st argument to functions
        a1  |-> 11,   \* used to pass 2nd argument to functions
        a2  |-> 12,
        a3  |-> 13,
        a4  |-> 14,
        a5  |-> 15,
        a6  |-> 16,
        a7  |-> 17,
        s2  |-> 18,
        s3  |-> 19,
        s4  |-> 20,
        s5  |-> 21,
        s6  |-> 22,
        s7  |-> 23,
        s8  |-> 24,
        s9  |-> 25,
        s10 |-> 26,
        s11 |-> 27,
        t3  |-> 28,
        t4  |-> 29,
        t5  |-> 30,
        t6  |-> 31,

        \* floating-point registers
        ft0  |-> 100,
        fa0  |-> 110,
        fs0  |-> 120,
        fs1  |-> 121,
        fs2  |-> 122,
        fs3  |-> 123,
        fs4  |-> 124,
        fs5  |-> 125,
        fs6  |-> 126,
        fs7  |-> 127,
        fs8  |-> 128,
        fs9  |-> 129,
        fs10 |-> 130,
        fs11 |-> 131
    ];

define
    CALLEE_SAVED == {
        "ra", "sp", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
        "fs0", "fs1", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7", "fs8", "fs9", "fs10", "fs11"}
    init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
    callee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]
end define;

macro inc(reg) begin
    registers[reg] := registers[reg] + 1;
end macro;

\* sd src, offset(base) / fsd src, offset(base)
\*
\* [base + offset] = src;
macro sd(src, offset, base) begin
    Context[registers[base] + offset] := registers[src];
end macro;

\* ld dst, offset(base) / fld dst, offset(base)
\*
\* dst = [base + offset];
macro ld(dst, offset, base) begin
    registers[dst] := Context[registers[base] + offset];
end macro;

procedure save_context()
begin
    \* Store general purpose registers.
    S000: sd("ra",     0, "a0");
    S001: sd("sp",     8, "a0");
    S002: sd("s0",    16, "a0");
    S003: sd("s1",    24, "a0");
    S004: sd("s2",    32, "a0");
    S005: sd("s3",    40, "a0");
    S006: sd("s4",    48, "a0");
    S007: sd("s5",    56, "a0");
    S008: sd("s6",    64, "a0");
    S009: sd("s7",    72, "a0");
    S010: sd("s8",    80, "a0");
    S011: sd("s9",    88, "a0");
    S012: sd("s10",   96, "a0");
    S013: sd("s11",  104, "a0");

    \* Store floating-point registers.
    S014: sd("fs0",  112, "a0");
    S015: sd("fs1",  120, "a0");
    S016: sd("fs2",  128, "a0");
    S017: sd("fs3",  136, "a0");
    S018: sd("fs4",  144, "a0");
    S019: sd("fs5",  152, "a0");
    S020: sd("fs6",  160, "a0");
    S021: sd("fs7",  168, "a0");
    S022: sd("fs8",  176, "a0");
    S023: sd("fs9",  184, "a0");
    S024: sd("fs10", 192, "a0");
    S025: sd("fs11", 200, "a0");
    return;
end procedure;

procedure restore_context()
begin
    \* Load general purpose registers.
    R000: ld("ra",     0, "a1");
    R001: ld("sp",     8, "a1");
    R002: ld("s0",    16, "a1");
    R003: ld("s1",    24, "a1");
    R004: ld("s2",    32, "a1");
    R005: ld("s3",    40, "a1");
    R006: ld("s4",    48, "a1");
    R007: ld("s5",    56, "a1");
    R008: ld("s6",    64, "a1");
    R009: ld("s7",    72, "a1");
    R010: ld("s8",    80, "a1");
    R011: ld("s9",    88, "a1");
    R012: ld("s10",   96, "a1");
    R013: ld("s11",  104, "a1");

    \* Load floating-point registers.
    R014: ld("fs0",  112, "a1");
    R015: ld("fs1",  120, "a1");
    R016: ld("fs2",  128, "a1");
    R017: ld("fs3",  136, "a1");
    R018: ld("fs4",  144, "a1");
    R019: ld("fs5",  152, "a1");
    R020: ld("fs6",  160, "a1");
    R021: ld("fs7",  168, "a1");
    R022: ld("fs8",  176, "a1");
    R023: ld("fs9",  184, "a1");
    R024: ld("fs10", 192, "a1");
    R025: ld("fs11", 200, "a1");
    return;
end procedure;

procedure update()
begin
    H000: inc("ra");
    H001: inc("sp");
    H002: inc("gp");
    H003: inc("tp");
    H004: inc("t0");
    H005: inc("t1");
    H006: inc("t2");
    H007: inc("s0");
    H008: inc("s1");
    H009: inc("a0");
    H010: inc("a1");
    H011: inc("a2");
    H012: inc("a3");
    H013: inc("a4");
    H014: inc("a5");
    H015: inc("a6");
    H016: inc("a7");
    H017: inc("s2");
    H018: inc("s3");
    H019: inc("s4");
    H020: inc("s5");
    H021: inc("s6");
    H022: inc("s7");
    H023: inc("s8");
    H024: inc("s9");
    H025: inc("s10");
    H026: inc("s11");
    H027: inc("t3");
    H028: inc("t4");
    H029: inc("t5");
    H030: inc("t6");
    H031: inc("ft0");
    H032: inc("fa0");
    H033: inc("fs0");
    H034: inc("fs1");
    H035: inc("fs2");
    H036: inc("fs3");
    H037: inc("fs4");
    H038: inc("fs5");
    H039: inc("fs6");
    H040: inc("fs7");
    H041: inc("fs8");
    H042: inc("fs9");
    H043: inc("fs10");
    H044: inc("fs11");
    return;
end procedure;

procedure test()
variables
    start_ctx = callee_saved_registers,
    a0,
begin
    start_test:
        Context := init_context;
        a0 := registers["a0"];

    call_save_registers:
        call save_context();

    call_update:
        call update();

    init_a1:
        registers["a1"] := a0;

    call_restore_registers:
        call restore_context();

    end_test:
        assert(callee_saved_registers = start_ctx);

    return;
end procedure;

begin
    check1:
        call test();
end algorithm;*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES Context, registers, pc, stack

(* define statement *)
CALLEE_SAVED == {
    "ra", "sp", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
    "fs0", "fs1", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7", "fs8", "fs9", "fs10", "fs11"}
init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
callee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]

VARIABLES start_ctx, a0

vars == << Context, registers, pc, stack, start_ctx, a0 >>

Init == (* Global variables *)
        /\ Context = defaultInitValue
        /\ registers = [
                           ra |-> 1,
                           sp |-> 2,
                           gp |-> 3,
                           tp |-> 4,
                           t0 |-> 5,
                           t1 |-> 6,
                           t2 |-> 7,
                           s0 |-> 8,
                           s1 |-> 9,
                           a0 |-> 0,
                           a1 |-> 11,
                           a2 |-> 12,
                           a3 |-> 13,
                           a4 |-> 14,
                           a5 |-> 15,
                           a6 |-> 16,
                           a7 |-> 17,
                           s2 |-> 18,
                           s3 |-> 19,
                           s4 |-> 20,
                           s5 |-> 21,
                           s6 |-> 22,
                           s7 |-> 23,
                           s8 |-> 24,
                           s9 |-> 25,
                           s10 |-> 26,
                           s11 |-> 27,
                           t3 |-> 28,
                           t4 |-> 29,
                           t5 |-> 30,
                           t6 |-> 31,
                           ft0 |-> 100,
                           fa0 |-> 110,
                           fs0 |-> 120,
                           fs1 |-> 121,
                           fs2 |-> 122,
                           fs3 |-> 123,
                           fs4 |-> 124,
                           fs5 |-> 125,
                           fs6 |-> 126,
                           fs7 |-> 127,
                           fs8 |-> 128,
                           fs9 |-> 129,
                           fs10 |-> 130,
                           fs11 |-> 131
                       ]
        (* Procedure test *)
        /\ start_ctx = callee_saved_registers
        /\ a0 = defaultInitValue
        /\ stack = << >>
        /\ pc = "check1"

S000 == /\ pc = "S000"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 0] = registers["ra"]]
        /\ pc' = "S001"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S001 == /\ pc = "S001"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 8] = registers["sp"]]
        /\ pc' = "S002"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S002 == /\ pc = "S002"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 16] = registers["s0"]]
        /\ pc' = "S003"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S003 == /\ pc = "S003"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 24] = registers["s1"]]
        /\ pc' = "S004"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S004 == /\ pc = "S004"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 32] = registers["s2"]]
        /\ pc' = "S005"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S005 == /\ pc = "S005"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 40] = registers["s3"]]
        /\ pc' = "S006"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S006 == /\ pc = "S006"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 48] = registers["s4"]]
        /\ pc' = "S007"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S007 == /\ pc = "S007"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 56] = registers["s5"]]
        /\ pc' = "S008"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S008 == /\ pc = "S008"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 64] = registers["s6"]]
        /\ pc' = "S009"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S009 == /\ pc = "S009"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 72] = registers["s7"]]
        /\ pc' = "S010"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S010 == /\ pc = "S010"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 80] = registers["s8"]]
        /\ pc' = "S011"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S011 == /\ pc = "S011"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 88] = registers["s9"]]
        /\ pc' = "S012"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S012 == /\ pc = "S012"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 96] = registers["s10"]]
        /\ pc' = "S013"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S013 == /\ pc = "S013"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 104] = registers["s11"]]
        /\ pc' = "S014"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S014 == /\ pc = "S014"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 112] = registers["fs0"]]
        /\ pc' = "S015"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S015 == /\ pc = "S015"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 120] = registers["fs1"]]
        /\ pc' = "S016"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S016 == /\ pc = "S016"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 128] = registers["fs2"]]
        /\ pc' = "S017"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S017 == /\ pc = "S017"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 136] = registers["fs3"]]
        /\ pc' = "S018"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S018 == /\ pc = "S018"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 144] = registers["fs4"]]
        /\ pc' = "S019"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S019 == /\ pc = "S019"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 152] = registers["fs5"]]
        /\ pc' = "S020"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S020 == /\ pc = "S020"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 160] = registers["fs6"]]
        /\ pc' = "S021"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S021 == /\ pc = "S021"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 168] = registers["fs7"]]
        /\ pc' = "S022"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S022 == /\ pc = "S022"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 176] = registers["fs8"]]
        /\ pc' = "S023"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S023 == /\ pc = "S023"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 184] = registers["fs9"]]
        /\ pc' = "S024"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S024 == /\ pc = "S024"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 192] = registers["fs10"]]
        /\ pc' = "S025"
        /\ UNCHANGED << registers, stack, start_ctx, a0 >>

S025 == /\ pc = "S025"
        /\ Context' = [Context EXCEPT ![registers["a0"] + 200] = registers["fs11"]]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << registers, start_ctx, a0 >>

save_context == S000 \/ S001 \/ S002 \/ S003 \/ S004 \/ S005 \/ S006 \/ S007
                \/ S008 \/ S009 \/ S010 \/ S011 \/ S012 \/ S013 \/ S014
                \/ S015 \/ S016 \/ S017 \/ S018 \/ S019 \/ S020 \/ S021
                \/ S022 \/ S023 \/ S024 \/ S025

R000 == /\ pc = "R000"
        /\ registers' = [registers EXCEPT !["ra"] = Context[registers["a1"] + 0]]
        /\ pc' = "R001"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R001 == /\ pc = "R001"
        /\ registers' = [registers EXCEPT !["sp"] = Context[registers["a1"] + 8]]
        /\ pc' = "R002"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R002 == /\ pc = "R002"
        /\ registers' = [registers EXCEPT !["s0"] = Context[registers["a1"] + 16]]
        /\ pc' = "R003"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R003 == /\ pc = "R003"
        /\ registers' = [registers EXCEPT !["s1"] = Context[registers["a1"] + 24]]
        /\ pc' = "R004"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R004 == /\ pc = "R004"
        /\ registers' = [registers EXCEPT !["s2"] = Context[registers["a1"] + 32]]
        /\ pc' = "R005"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R005 == /\ pc = "R005"
        /\ registers' = [registers EXCEPT !["s3"] = Context[registers["a1"] + 40]]
        /\ pc' = "R006"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R006 == /\ pc = "R006"
        /\ registers' = [registers EXCEPT !["s4"] = Context[registers["a1"] + 48]]
        /\ pc' = "R007"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R007 == /\ pc = "R007"
        /\ registers' = [registers EXCEPT !["s5"] = Context[registers["a1"] + 56]]
        /\ pc' = "R008"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R008 == /\ pc = "R008"
        /\ registers' = [registers EXCEPT !["s6"] = Context[registers["a1"] + 64]]
        /\ pc' = "R009"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R009 == /\ pc = "R009"
        /\ registers' = [registers EXCEPT !["s7"] = Context[registers["a1"] + 72]]
        /\ pc' = "R010"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R010 == /\ pc = "R010"
        /\ registers' = [registers EXCEPT !["s8"] = Context[registers["a1"] + 80]]
        /\ pc' = "R011"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R011 == /\ pc = "R011"
        /\ registers' = [registers EXCEPT !["s9"] = Context[registers["a1"] + 88]]
        /\ pc' = "R012"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R012 == /\ pc = "R012"
        /\ registers' = [registers EXCEPT !["s10"] = Context[registers["a1"] + 96]]
        /\ pc' = "R013"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R013 == /\ pc = "R013"
        /\ registers' = [registers EXCEPT !["s11"] = Context[registers["a1"] + 104]]
        /\ pc' = "R014"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R014 == /\ pc = "R014"
        /\ registers' = [registers EXCEPT !["fs0"] = Context[registers["a1"] + 112]]
        /\ pc' = "R015"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R015 == /\ pc = "R015"
        /\ registers' = [registers EXCEPT !["fs1"] = Context[registers["a1"] + 120]]
        /\ pc' = "R016"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R016 == /\ pc = "R016"
        /\ registers' = [registers EXCEPT !["fs2"] = Context[registers["a1"] + 128]]
        /\ pc' = "R017"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R017 == /\ pc = "R017"
        /\ registers' = [registers EXCEPT !["fs3"] = Context[registers["a1"] + 136]]
        /\ pc' = "R018"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R018 == /\ pc = "R018"
        /\ registers' = [registers EXCEPT !["fs4"] = Context[registers["a1"] + 144]]
        /\ pc' = "R019"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R019 == /\ pc = "R019"
        /\ registers' = [registers EXCEPT !["fs5"] = Context[registers["a1"] + 152]]
        /\ pc' = "R020"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R020 == /\ pc = "R020"
        /\ registers' = [registers EXCEPT !["fs6"] = Context[registers["a1"] + 160]]
        /\ pc' = "R021"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R021 == /\ pc = "R021"
        /\ registers' = [registers EXCEPT !["fs7"] = Context[registers["a1"] + 168]]
        /\ pc' = "R022"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R022 == /\ pc = "R022"
        /\ registers' = [registers EXCEPT !["fs8"] = Context[registers["a1"] + 176]]
        /\ pc' = "R023"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R023 == /\ pc = "R023"
        /\ registers' = [registers EXCEPT !["fs9"] = Context[registers["a1"] + 184]]
        /\ pc' = "R024"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R024 == /\ pc = "R024"
        /\ registers' = [registers EXCEPT !["fs10"] = Context[registers["a1"] + 192]]
        /\ pc' = "R025"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

R025 == /\ pc = "R025"
        /\ registers' = [registers EXCEPT !["fs11"] = Context[registers["a1"] + 200]]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, start_ctx, a0 >>

restore_context == R000 \/ R001 \/ R002 \/ R003 \/ R004 \/ R005 \/ R006 \/ R007
                   \/ R008 \/ R009 \/ R010 \/ R011 \/ R012 \/ R013 \/ R014
                   \/ R015 \/ R016 \/ R017 \/ R018 \/ R019 \/ R020 \/ R021
                   \/ R022 \/ R023 \/ R024 \/ R025

H000 == /\ pc = "H000"
        /\ registers' = [registers EXCEPT !["ra"] = registers["ra"] + 1]
        /\ pc' = "H001"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H001 == /\ pc = "H001"
        /\ registers' = [registers EXCEPT !["sp"] = registers["sp"] + 1]
        /\ pc' = "H002"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H002 == /\ pc = "H002"
        /\ registers' = [registers EXCEPT !["gp"] = registers["gp"] + 1]
        /\ pc' = "H003"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H003 == /\ pc = "H003"
        /\ registers' = [registers EXCEPT !["tp"] = registers["tp"] + 1]
        /\ pc' = "H004"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H004 == /\ pc = "H004"
        /\ registers' = [registers EXCEPT !["t0"] = registers["t0"] + 1]
        /\ pc' = "H005"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H005 == /\ pc = "H005"
        /\ registers' = [registers EXCEPT !["t1"] = registers["t1"] + 1]
        /\ pc' = "H006"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H006 == /\ pc = "H006"
        /\ registers' = [registers EXCEPT !["t2"] = registers["t2"] + 1]
        /\ pc' = "H007"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H007 == /\ pc = "H007"
        /\ registers' = [registers EXCEPT !["s0"] = registers["s0"] + 1]
        /\ pc' = "H008"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H008 == /\ pc = "H008"
        /\ registers' = [registers EXCEPT !["s1"] = registers["s1"] + 1]
        /\ pc' = "H009"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H009 == /\ pc = "H009"
        /\ registers' = [registers EXCEPT !["a0"] = registers["a0"] + 1]
        /\ pc' = "H010"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H010 == /\ pc = "H010"
        /\ registers' = [registers EXCEPT !["a1"] = registers["a1"] + 1]
        /\ pc' = "H011"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H011 == /\ pc = "H011"
        /\ registers' = [registers EXCEPT !["a2"] = registers["a2"] + 1]
        /\ pc' = "H012"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H012 == /\ pc = "H012"
        /\ registers' = [registers EXCEPT !["a3"] = registers["a3"] + 1]
        /\ pc' = "H013"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H013 == /\ pc = "H013"
        /\ registers' = [registers EXCEPT !["a4"] = registers["a4"] + 1]
        /\ pc' = "H014"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H014 == /\ pc = "H014"
        /\ registers' = [registers EXCEPT !["a5"] = registers["a5"] + 1]
        /\ pc' = "H015"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H015 == /\ pc = "H015"
        /\ registers' = [registers EXCEPT !["a6"] = registers["a6"] + 1]
        /\ pc' = "H016"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H016 == /\ pc = "H016"
        /\ registers' = [registers EXCEPT !["a7"] = registers["a7"] + 1]
        /\ pc' = "H017"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H017 == /\ pc = "H017"
        /\ registers' = [registers EXCEPT !["s2"] = registers["s2"] + 1]
        /\ pc' = "H018"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H018 == /\ pc = "H018"
        /\ registers' = [registers EXCEPT !["s3"] = registers["s3"] + 1]
        /\ pc' = "H019"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H019 == /\ pc = "H019"
        /\ registers' = [registers EXCEPT !["s4"] = registers["s4"] + 1]
        /\ pc' = "H020"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H020 == /\ pc = "H020"
        /\ registers' = [registers EXCEPT !["s5"] = registers["s5"] + 1]
        /\ pc' = "H021"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H021 == /\ pc = "H021"
        /\ registers' = [registers EXCEPT !["s6"] = registers["s6"] + 1]
        /\ pc' = "H022"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H022 == /\ pc = "H022"
        /\ registers' = [registers EXCEPT !["s7"] = registers["s7"] + 1]
        /\ pc' = "H023"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H023 == /\ pc = "H023"
        /\ registers' = [registers EXCEPT !["s8"] = registers["s8"] + 1]
        /\ pc' = "H024"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H024 == /\ pc = "H024"
        /\ registers' = [registers EXCEPT !["s9"] = registers["s9"] + 1]
        /\ pc' = "H025"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H025 == /\ pc = "H025"
        /\ registers' = [registers EXCEPT !["s10"] = registers["s10"] + 1]
        /\ pc' = "H026"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H026 == /\ pc = "H026"
        /\ registers' = [registers EXCEPT !["s11"] = registers["s11"] + 1]
        /\ pc' = "H027"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H027 == /\ pc = "H027"
        /\ registers' = [registers EXCEPT !["t3"] = registers["t3"] + 1]
        /\ pc' = "H028"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H028 == /\ pc = "H028"
        /\ registers' = [registers EXCEPT !["t4"] = registers["t4"] + 1]
        /\ pc' = "H029"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H029 == /\ pc = "H029"
        /\ registers' = [registers EXCEPT !["t5"] = registers["t5"] + 1]
        /\ pc' = "H030"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H030 == /\ pc = "H030"
        /\ registers' = [registers EXCEPT !["t6"] = registers["t6"] + 1]
        /\ pc' = "H031"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H031 == /\ pc = "H031"
        /\ registers' = [registers EXCEPT !["ft0"] = registers["ft0"] + 1]
        /\ pc' = "H032"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H032 == /\ pc = "H032"
        /\ registers' = [registers EXCEPT !["fa0"] = registers["fa0"] + 1]
        /\ pc' = "H033"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H033 == /\ pc = "H033"
        /\ registers' = [registers EXCEPT !["fs0"] = registers["fs0"] + 1]
        /\ pc' = "H034"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H034 == /\ pc = "H034"
        /\ registers' = [registers EXCEPT !["fs1"] = registers["fs1"] + 1]
        /\ pc' = "H035"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H035 == /\ pc = "H035"
        /\ registers' = [registers EXCEPT !["fs2"] = registers["fs2"] + 1]
        /\ pc' = "H036"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H036 == /\ pc = "H036"
        /\ registers' = [registers EXCEPT !["fs3"] = registers["fs3"] + 1]
        /\ pc' = "H037"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H037 == /\ pc = "H037"
        /\ registers' = [registers EXCEPT !["fs4"] = registers["fs4"] + 1]
        /\ pc' = "H038"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H038 == /\ pc = "H038"
        /\ registers' = [registers EXCEPT !["fs5"] = registers["fs5"] + 1]
        /\ pc' = "H039"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H039 == /\ pc = "H039"
        /\ registers' = [registers EXCEPT !["fs6"] = registers["fs6"] + 1]
        /\ pc' = "H040"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H040 == /\ pc = "H040"
        /\ registers' = [registers EXCEPT !["fs7"] = registers["fs7"] + 1]
        /\ pc' = "H041"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H041 == /\ pc = "H041"
        /\ registers' = [registers EXCEPT !["fs8"] = registers["fs8"] + 1]
        /\ pc' = "H042"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H042 == /\ pc = "H042"
        /\ registers' = [registers EXCEPT !["fs9"] = registers["fs9"] + 1]
        /\ pc' = "H043"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H043 == /\ pc = "H043"
        /\ registers' = [registers EXCEPT !["fs10"] = registers["fs10"] + 1]
        /\ pc' = "H044"
        /\ UNCHANGED << Context, stack, start_ctx, a0 >>

H044 == /\ pc = "H044"
        /\ registers' = [registers EXCEPT !["fs11"] = registers["fs11"] + 1]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, start_ctx, a0 >>

update == H000 \/ H001 \/ H002 \/ H003 \/ H004 \/ H005 \/ H006 \/ H007
          \/ H008 \/ H009 \/ H010 \/ H011 \/ H012 \/ H013 \/ H014
          \/ H015 \/ H016 \/ H017 \/ H018 \/ H019 \/ H020 \/ H021
          \/ H022 \/ H023 \/ H024 \/ H025 \/ H026 \/ H027 \/ H028
          \/ H029 \/ H030 \/ H031 \/ H032 \/ H033 \/ H034 \/ H035
          \/ H036 \/ H037 \/ H038 \/ H039 \/ H040 \/ H041 \/ H042
          \/ H043 \/ H044

start_test == /\ pc = "start_test"
              /\ Context' = init_context
              /\ a0' = registers["a0"]
              /\ pc' = "call_save_registers"
              /\ UNCHANGED << registers, stack, start_ctx >>

call_save_registers == /\ pc = "call_save_registers"
                       /\ stack' = << [ procedure |->  "save_context",
                                        pc        |->  "call_update" ] >>
                                    \o stack
                       /\ pc' = "S000"
                       /\ UNCHANGED << Context, registers, start_ctx, a0 >>

call_update == /\ pc = "call_update"
               /\ stack' = << [ procedure |->  "update",
                                pc        |->  "init_a1" ] >>
                            \o stack
               /\ pc' = "H000"
               /\ UNCHANGED << Context, registers, start_ctx, a0 >>

init_a1 == /\ pc = "init_a1"
           /\ registers' = [registers EXCEPT !["a1"] = a0]
           /\ pc' = "call_restore_registers"
           /\ UNCHANGED << Context, stack, start_ctx, a0 >>

call_restore_registers == /\ pc = "call_restore_registers"
                          /\ stack' = << [ procedure |->  "restore_context",
                                           pc        |->  "end_test" ] >>
                                       \o stack
                          /\ pc' = "R000"
                          /\ UNCHANGED << Context, registers, start_ctx, a0 >>

end_test == /\ pc = "end_test"
            /\ Assert((callee_saved_registers = start_ctx), 
                      "Failure of assertion at line 228, column 9.")
            /\ pc' = Head(stack).pc
            /\ start_ctx' = Head(stack).start_ctx
            /\ a0' = Head(stack).a0
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, registers >>

test == start_test \/ call_save_registers \/ call_update \/ init_a1
           \/ call_restore_registers \/ end_test

check1 == /\ pc = "check1"
          /\ stack' = << [ procedure |->  "test",
                           pc        |->  "Done",
                           start_ctx |->  start_ctx,
                           a0        |->  a0 ] >>
                       \o stack
          /\ start_ctx' = callee_saved_registers
          /\ a0' = defaultInitValue
          /\ pc' = "start_test"
          /\ UNCHANGED << Context, registers >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == save_context \/ restore_context \/ update \/ test \/ check1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
