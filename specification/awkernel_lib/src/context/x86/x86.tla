----------------- MODULE x86 ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT SIZE_CONTEXT

(*--algorithm x86

variables
    Context;

    registers = [
        \* general purpose registers
        rax |-> 0,
        rbx |-> 1,
        rcx |-> 2,
        rdx |-> 3,
        rdi |-> 4,   \* used to pass 1st argument to functions
        rsi |-> 5,   \* used to pass 2nd argument to functions
        rsp |-> 6,
        rbp |-> 7,
        r8  |-> 8,
        r9  |-> 9,
        r10 |-> 10,
        r11 |-> 11,
        r12 |-> 12,
        r13 |-> 13,
        r14 |-> 14,
        r15 |-> 15
    ];

define
    CALLEE_SAVED == {"rbx", "rsp", "rbp", "r12", "r13", "r14", "r15"}
    init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
    callee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]
end define;

macro inc(reg) begin
    registers[reg] := registers[reg] + 1;
end macro;

macro mov0(offset, dst, src) begin
    Context[registers[dst] + offset] := registers[src];
end macro;

macro mov1(dst, offset, src) begin
    registers[dst] := Context[registers[src] + offset];
end macro;

procedure save_context()
begin    
    \* Store general purpose registers
    S000: mov0(0,  "rdi", "rbx");
    S001: mov0(8,  "rdi", "rsp");
    S002: mov0(16, "rdi", "rbp");
    S003: mov0(24, "rdi", "r12");
    S004: mov0(32, "rdi", "r13");
    S005: mov0(40, "rdi", "r14");
    S006: mov0(48, "rdi", "r15");
    return;
end procedure;

procedure restore_context()
begin        
    \* Restore general purpose registers
    R000: mov1("rbx", 0,  "rsi");
    R001: mov1("rsp", 8,  "rsi");
    R002: mov1("rbp", 16, "rsi");
    R003: mov1("r12", 24, "rsi");
    R004: mov1("r13", 32, "rsi");
    R005: mov1("r14", 40, "rsi");
    R006: mov1("r15", 48, "rsi");
    return;
end procedure;

procedure update()
begin
    H000: inc("rax");
    H001: inc("rbx");
    H002: inc("rcx");
    H003: inc("rdx");
    H004: inc("rdi");
    H005: inc("rsi");
    H006: inc("rsp");
    H007: inc("rbp");
    H008: inc("r8");
    H009: inc("r9");
    H010: inc("r10");
    H011: inc("r11");
    H012: inc("r12");
    H013: inc("r13");
    H014: inc("r14");
    H015: inc("r15");
    return;
end procedure;

procedure test()
variables
    start_ctx = callee_saved_registers,
    rdi,
begin
    start_test:
        Context := init_context;
        rdi := registers["rdi"];
    
    call_save_registers:
        call save_context();
    
    call_update:
        call update();
    
    init_rsi:
        registers["rsi"] := rdi;
    
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
\* BEGIN TRANSLATION (chksum(pcal) = "f603a53f" /\ chksum(tla) = "e197210")
CONSTANT defaultInitValue
VARIABLES Context, registers, pc, stack

(* define statement *)
CALLEE_SAVED == {"rbx", "rsp", "rbp", "r12", "r13", "r14", "r15"}
init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
callee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]

VARIABLES start_ctx, rdi

vars == << Context, registers, pc, stack, start_ctx, rdi >>

Init == (* Global variables *)
        /\ Context = defaultInitValue
        /\ registers =             [
                       
                           rax |-> 0,
                           rbx |-> 1,
                           rcx |-> 2,
                           rdx |-> 3,
                           rdi |-> 4,
                           rsi |-> 5,
                           rsp |-> 6,
                           rbp |-> 7,
                           r8  |-> 8,
                           r9  |-> 9,
                           r10 |-> 10,
                           r11 |-> 11,
                           r12 |-> 12,
                           r13 |-> 13,
                           r14 |-> 14,
                           r15 |-> 15
                       ]
        (* Procedure test *)
        /\ start_ctx = callee_saved_registers
        /\ rdi = defaultInitValue
        /\ stack = << >>
        /\ pc = "check1"

S000 == /\ pc = "S000"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 0] = registers["rbx"]]
        /\ pc' = "S001"
        /\ UNCHANGED << registers, stack, start_ctx, rdi >>

S001 == /\ pc = "S001"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 8] = registers["rsp"]]
        /\ pc' = "S002"
        /\ UNCHANGED << registers, stack, start_ctx, rdi >>

S002 == /\ pc = "S002"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 16] = registers["rbp"]]
        /\ pc' = "S003"
        /\ UNCHANGED << registers, stack, start_ctx, rdi >>

S003 == /\ pc = "S003"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 24] = registers["r12"]]
        /\ pc' = "S004"
        /\ UNCHANGED << registers, stack, start_ctx, rdi >>

S004 == /\ pc = "S004"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 32] = registers["r13"]]
        /\ pc' = "S005"
        /\ UNCHANGED << registers, stack, start_ctx, rdi >>

S005 == /\ pc = "S005"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 40] = registers["r14"]]
        /\ pc' = "S006"
        /\ UNCHANGED << registers, stack, start_ctx, rdi >>

S006 == /\ pc = "S006"
        /\ Context' = [Context EXCEPT ![registers["rdi"] + 48] = registers["r15"]]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << registers, start_ctx, rdi >>

save_context == S000 \/ S001 \/ S002 \/ S003 \/ S004 \/ S005 \/ S006

R000 == /\ pc = "R000"
        /\ registers' = [registers EXCEPT !["rbx"] = Context[registers["rsi"] + 0]]
        /\ pc' = "R001"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

R001 == /\ pc = "R001"
        /\ registers' = [registers EXCEPT !["rsp"] = Context[registers["rsi"] + 8]]
        /\ pc' = "R002"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

R002 == /\ pc = "R002"
        /\ registers' = [registers EXCEPT !["rbp"] = Context[registers["rsi"] + 16]]
        /\ pc' = "R003"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

R003 == /\ pc = "R003"
        /\ registers' = [registers EXCEPT !["r12"] = Context[registers["rsi"] + 24]]
        /\ pc' = "R004"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

R004 == /\ pc = "R004"
        /\ registers' = [registers EXCEPT !["r13"] = Context[registers["rsi"] + 32]]
        /\ pc' = "R005"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

R005 == /\ pc = "R005"
        /\ registers' = [registers EXCEPT !["r14"] = Context[registers["rsi"] + 40]]
        /\ pc' = "R006"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

R006 == /\ pc = "R006"
        /\ registers' = [registers EXCEPT !["r15"] = Context[registers["rsi"] + 48]]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, start_ctx, rdi >>

restore_context == R000 \/ R001 \/ R002 \/ R003 \/ R004 \/ R005 \/ R006

H000 == /\ pc = "H000"
        /\ registers' = [registers EXCEPT !["rax"] = registers["rax"] + 1]
        /\ pc' = "H001"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H001 == /\ pc = "H001"
        /\ registers' = [registers EXCEPT !["rbx"] = registers["rbx"] + 1]
        /\ pc' = "H002"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H002 == /\ pc = "H002"
        /\ registers' = [registers EXCEPT !["rcx"] = registers["rcx"] + 1]
        /\ pc' = "H003"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H003 == /\ pc = "H003"
        /\ registers' = [registers EXCEPT !["rdx"] = registers["rdx"] + 1]
        /\ pc' = "H004"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H004 == /\ pc = "H004"
        /\ registers' = [registers EXCEPT !["rdi"] = registers["rdi"] + 1]
        /\ pc' = "H005"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H005 == /\ pc = "H005"
        /\ registers' = [registers EXCEPT !["rsi"] = registers["rsi"] + 1]
        /\ pc' = "H006"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H006 == /\ pc = "H006"
        /\ registers' = [registers EXCEPT !["rsp"] = registers["rsp"] + 1]
        /\ pc' = "H007"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H007 == /\ pc = "H007"
        /\ registers' = [registers EXCEPT !["rbp"] = registers["rbp"] + 1]
        /\ pc' = "H008"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H008 == /\ pc = "H008"
        /\ registers' = [registers EXCEPT !["r8"] = registers["r8"] + 1]
        /\ pc' = "H009"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H009 == /\ pc = "H009"
        /\ registers' = [registers EXCEPT !["r9"] = registers["r9"] + 1]
        /\ pc' = "H010"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H010 == /\ pc = "H010"
        /\ registers' = [registers EXCEPT !["r10"] = registers["r10"] + 1]
        /\ pc' = "H011"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H011 == /\ pc = "H011"
        /\ registers' = [registers EXCEPT !["r11"] = registers["r11"] + 1]
        /\ pc' = "H012"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H012 == /\ pc = "H012"
        /\ registers' = [registers EXCEPT !["r12"] = registers["r12"] + 1]
        /\ pc' = "H013"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H013 == /\ pc = "H013"
        /\ registers' = [registers EXCEPT !["r13"] = registers["r13"] + 1]
        /\ pc' = "H014"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H014 == /\ pc = "H014"
        /\ registers' = [registers EXCEPT !["r14"] = registers["r14"] + 1]
        /\ pc' = "H015"
        /\ UNCHANGED << Context, stack, start_ctx, rdi >>

H015 == /\ pc = "H015"
        /\ registers' = [registers EXCEPT !["r15"] = registers["r15"] + 1]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, start_ctx, rdi >>

update == H000 \/ H001 \/ H002 \/ H003 \/ H004 \/ H005 \/ H006 \/ H007
             \/ H008 \/ H009 \/ H010 \/ H011 \/ H012 \/ H013 \/ H014
             \/ H015

start_test == /\ pc = "start_test"
              /\ Context' = init_context
              /\ rdi' = registers["rdi"]
              /\ pc' = "call_save_registers"
              /\ UNCHANGED << registers, stack, start_ctx >>

call_save_registers == /\ pc = "call_save_registers"
                       /\ stack' = << [ procedure |->  "save_context",
                                        pc        |->  "call_update" ] >>
                                    \o stack
                       /\ pc' = "S000"
                       /\ UNCHANGED << Context, registers, start_ctx, rdi >>

call_update == /\ pc = "call_update"
               /\ stack' = << [ procedure |->  "update",
                                pc        |->  "init_rsi" ] >>
                            \o stack
               /\ pc' = "H000"
               /\ UNCHANGED << Context, registers, start_ctx, rdi >>

init_rsi == /\ pc = "init_rsi"
            /\ registers' = [registers EXCEPT !["rsi"] = rdi]
            /\ pc' = "call_restore_registers"
            /\ UNCHANGED << Context, stack, start_ctx, rdi >>

call_restore_registers == /\ pc = "call_restore_registers"
                          /\ stack' = << [ procedure |->  "restore_context",
                                           pc        |->  "end_test" ] >>
                                       \o stack
                          /\ pc' = "R000"
                          /\ UNCHANGED << Context, registers, start_ctx, rdi >>

end_test == /\ pc = "end_test"
            /\ Assert((callee_saved_registers = start_ctx), 
                      "Failure of assertion at line 118, column 9.")
            /\ pc' = Head(stack).pc
            /\ start_ctx' = Head(stack).start_ctx
            /\ rdi' = Head(stack).rdi
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, registers >>

test == start_test \/ call_save_registers \/ call_update \/ init_rsi
           \/ call_restore_registers \/ end_test

check1 == /\ pc = "check1"
          /\ stack' = << [ procedure |->  "test",
                           pc        |->  "Done",
                           start_ctx |->  start_ctx,
                           rdi       |->  rdi ] >>
                       \o stack
          /\ start_ctx' = callee_saved_registers
          /\ rdi' = defaultInitValue
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
