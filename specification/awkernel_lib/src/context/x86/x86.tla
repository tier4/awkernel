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
    CALLEE_SAVED == {"rbx", "rbp", "r12", "r13", "r14", "r15"}
    init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
    callee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]
end define;

macro inc(reg) begin
    registers[reg] := registers[reg] + 1;
end macro;

procedure push(reg)
variables
    addr
begin
    push0:
        addr := registers["rsp"];
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
    push1:
        Context[addr] := registers[reg];
    push2:
        registers["rsp"] := addr + 8;
    
    return;
end procedure;

procedure pop(reg)
variables
    addr
begin
    pop0:
        addr := registers["rsp"] - 8;
        assert 0 <= addr /\ addr < SIZE_CONTEXT;
    pop1:
        registers[reg] := Context[addr];
    pop2:
        registers["rsp"] := addr;
    
    return;
end procedure;

procedure save_context()
begin
    S000: registers["rsp"] := registers["rdi"];
    
    \* Store general purpose registers
    S100: call push("rbx");
    S101: call push("rbp");
    S102: call push("r12");
    S103: call push("r13");
    S104: call push("r14");
    S105: call push("r15");    
    return;
end procedure;

procedure restore_context()
begin
    R000: registers["rsp"] := registers["rsi"] + 8 * 6;
        
    \* Restore general purpose registers
    R100: call pop("r15");
    R101: call pop("r14");
    R102: call pop("r13");
    R103: call pop("r12");
    R107: call pop("rbp");
    R108: call pop("rbx");
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
    sp
begin
    start_test:
        Context := init_context;
        sp := registers["rsp"];
        registers["rdi"] := sp;
    
    call_save_registers:
        call save_context();
    
    call_update:
        call update();
    
    init_rsi:
        registers["rsi"] := sp;
    
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
\* BEGIN TRANSLATION (chksum(pcal) = "7941a75f" /\ chksum(tla) = "7c41ecab")
\* Procedure variable addr of procedure push at line 43 col 5 changed to addr_
\* Parameter reg of procedure push at line 41 col 16 changed to reg_
CONSTANT defaultInitValue
VARIABLES Context, registers, pc, stack

(* define statement *)
CALLEE_SAVED == {"rbx", "rbp", "r12", "r13", "r14", "r15"}
init_context == [x \in 0..(SIZE_CONTEXT - 1) |-> 0]
callee_saved_registers == [x \in CALLEE_SAVED |-> registers[x]]

VARIABLES reg_, addr_, reg, addr, start_ctx, sp

vars == << Context, registers, pc, stack, reg_, addr_, reg, addr, start_ctx, 
           sp >>

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
        (* Procedure push *)
        /\ reg_ = defaultInitValue
        /\ addr_ = defaultInitValue
        (* Procedure pop *)
        /\ reg = defaultInitValue
        /\ addr = defaultInitValue
        (* Procedure test *)
        /\ start_ctx = callee_saved_registers
        /\ sp = defaultInitValue
        /\ stack = << >>
        /\ pc = "check1"

push0 == /\ pc = "push0"
         /\ addr_' = registers["rsp"]
         /\ Assert(0 <= addr_' /\ addr_' < SIZE_CONTEXT, 
                   "Failure of assertion at line 47, column 9.")
         /\ pc' = "push1"
         /\ UNCHANGED << Context, registers, stack, reg_, reg, addr, start_ctx, 
                         sp >>

push1 == /\ pc = "push1"
         /\ Context' = [Context EXCEPT ![addr_] = registers[reg_]]
         /\ pc' = "push2"
         /\ UNCHANGED << registers, stack, reg_, addr_, reg, addr, start_ctx, 
                         sp >>

push2 == /\ pc = "push2"
         /\ registers' = [registers EXCEPT !["rsp"] = addr_ + 8]
         /\ pc' = Head(stack).pc
         /\ addr_' = Head(stack).addr_
         /\ reg_' = Head(stack).reg_
         /\ stack' = Tail(stack)
         /\ UNCHANGED << Context, reg, addr, start_ctx, sp >>

push == push0 \/ push1 \/ push2

pop0 == /\ pc = "pop0"
        /\ addr' = registers["rsp"] - 8
        /\ Assert(0 <= addr' /\ addr' < SIZE_CONTEXT, 
                  "Failure of assertion at line 62, column 9.")
        /\ pc' = "pop1"
        /\ UNCHANGED << Context, registers, stack, reg_, addr_, reg, start_ctx, 
                        sp >>

pop1 == /\ pc = "pop1"
        /\ registers' = [registers EXCEPT ![reg] = Context[addr]]
        /\ pc' = "pop2"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

pop2 == /\ pc = "pop2"
        /\ registers' = [registers EXCEPT !["rsp"] = addr]
        /\ pc' = Head(stack).pc
        /\ addr' = Head(stack).addr
        /\ reg' = Head(stack).reg
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg_, addr_, start_ctx, sp >>

pop == pop0 \/ pop1 \/ pop2

S000 == /\ pc = "S000"
        /\ registers' = [registers EXCEPT !["rsp"] = registers["rdi"]]
        /\ pc' = "S100"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

S100 == /\ pc = "S100"
        /\ /\ reg_' = "rbx"
           /\ stack' = << [ procedure |->  "push",
                            pc        |->  "S101",
                            addr_     |->  addr_,
                            reg_      |->  reg_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "push0"
        /\ UNCHANGED << Context, registers, reg, addr, start_ctx, sp >>

S101 == /\ pc = "S101"
        /\ /\ reg_' = "rbp"
           /\ stack' = << [ procedure |->  "push",
                            pc        |->  "S102",
                            addr_     |->  addr_,
                            reg_      |->  reg_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "push0"
        /\ UNCHANGED << Context, registers, reg, addr, start_ctx, sp >>

S102 == /\ pc = "S102"
        /\ /\ reg_' = "r12"
           /\ stack' = << [ procedure |->  "push",
                            pc        |->  "S103",
                            addr_     |->  addr_,
                            reg_      |->  reg_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "push0"
        /\ UNCHANGED << Context, registers, reg, addr, start_ctx, sp >>

S103 == /\ pc = "S103"
        /\ /\ reg_' = "r13"
           /\ stack' = << [ procedure |->  "push",
                            pc        |->  "S104",
                            addr_     |->  addr_,
                            reg_      |->  reg_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "push0"
        /\ UNCHANGED << Context, registers, reg, addr, start_ctx, sp >>

S104 == /\ pc = "S104"
        /\ /\ reg_' = "r14"
           /\ stack' = << [ procedure |->  "push",
                            pc        |->  "S105",
                            addr_     |->  addr_,
                            reg_      |->  reg_ ] >>
                        \o stack
        /\ addr_' = defaultInitValue
        /\ pc' = "push0"
        /\ UNCHANGED << Context, registers, reg, addr, start_ctx, sp >>

S105 == /\ pc = "S105"
        /\ /\ reg_' = "r15"
           /\ stack' = << [ procedure |->  "push",
                            pc        |->  Head(stack).pc,
                            addr_     |->  addr_,
                            reg_      |->  reg_ ] >>
                        \o Tail(stack)
        /\ addr_' = defaultInitValue
        /\ pc' = "push0"
        /\ UNCHANGED << Context, registers, reg, addr, start_ctx, sp >>

save_context == S000 \/ S100 \/ S101 \/ S102 \/ S103 \/ S104 \/ S105

R000 == /\ pc = "R000"
        /\ registers' = [registers EXCEPT !["rsp"] = registers["rsi"] + 8 * 6]
        /\ pc' = "R100"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

R100 == /\ pc = "R100"
        /\ /\ reg' = "r15"
           /\ stack' = << [ procedure |->  "pop",
                            pc        |->  "R101",
                            addr      |->  addr,
                            reg       |->  reg ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "pop0"
        /\ UNCHANGED << Context, registers, reg_, addr_, start_ctx, sp >>

R101 == /\ pc = "R101"
        /\ /\ reg' = "r14"
           /\ stack' = << [ procedure |->  "pop",
                            pc        |->  "R102",
                            addr      |->  addr,
                            reg       |->  reg ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "pop0"
        /\ UNCHANGED << Context, registers, reg_, addr_, start_ctx, sp >>

R102 == /\ pc = "R102"
        /\ /\ reg' = "r13"
           /\ stack' = << [ procedure |->  "pop",
                            pc        |->  "R103",
                            addr      |->  addr,
                            reg       |->  reg ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "pop0"
        /\ UNCHANGED << Context, registers, reg_, addr_, start_ctx, sp >>

R103 == /\ pc = "R103"
        /\ /\ reg' = "r12"
           /\ stack' = << [ procedure |->  "pop",
                            pc        |->  "R107",
                            addr      |->  addr,
                            reg       |->  reg ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "pop0"
        /\ UNCHANGED << Context, registers, reg_, addr_, start_ctx, sp >>

R107 == /\ pc = "R107"
        /\ /\ reg' = "rbp"
           /\ stack' = << [ procedure |->  "pop",
                            pc        |->  "R108",
                            addr      |->  addr,
                            reg       |->  reg ] >>
                        \o stack
        /\ addr' = defaultInitValue
        /\ pc' = "pop0"
        /\ UNCHANGED << Context, registers, reg_, addr_, start_ctx, sp >>

R108 == /\ pc = "R108"
        /\ /\ reg' = "rbx"
           /\ stack' = << [ procedure |->  "pop",
                            pc        |->  Head(stack).pc,
                            addr      |->  addr,
                            reg       |->  reg ] >>
                        \o Tail(stack)
        /\ addr' = defaultInitValue
        /\ pc' = "pop0"
        /\ UNCHANGED << Context, registers, reg_, addr_, start_ctx, sp >>

restore_context == R000 \/ R100 \/ R101 \/ R102 \/ R103 \/ R107 \/ R108

H000 == /\ pc = "H000"
        /\ registers' = [registers EXCEPT !["rax"] = registers["rax"] + 1]
        /\ pc' = "H001"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H001 == /\ pc = "H001"
        /\ registers' = [registers EXCEPT !["rbx"] = registers["rbx"] + 1]
        /\ pc' = "H002"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H002 == /\ pc = "H002"
        /\ registers' = [registers EXCEPT !["rcx"] = registers["rcx"] + 1]
        /\ pc' = "H003"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H003 == /\ pc = "H003"
        /\ registers' = [registers EXCEPT !["rdx"] = registers["rdx"] + 1]
        /\ pc' = "H004"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H004 == /\ pc = "H004"
        /\ registers' = [registers EXCEPT !["rdi"] = registers["rdi"] + 1]
        /\ pc' = "H005"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H005 == /\ pc = "H005"
        /\ registers' = [registers EXCEPT !["rsi"] = registers["rsi"] + 1]
        /\ pc' = "H006"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H006 == /\ pc = "H006"
        /\ registers' = [registers EXCEPT !["rsp"] = registers["rsp"] + 1]
        /\ pc' = "H007"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H007 == /\ pc = "H007"
        /\ registers' = [registers EXCEPT !["rbp"] = registers["rbp"] + 1]
        /\ pc' = "H008"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H008 == /\ pc = "H008"
        /\ registers' = [registers EXCEPT !["r8"] = registers["r8"] + 1]
        /\ pc' = "H009"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H009 == /\ pc = "H009"
        /\ registers' = [registers EXCEPT !["r9"] = registers["r9"] + 1]
        /\ pc' = "H010"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H010 == /\ pc = "H010"
        /\ registers' = [registers EXCEPT !["r10"] = registers["r10"] + 1]
        /\ pc' = "H011"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H011 == /\ pc = "H011"
        /\ registers' = [registers EXCEPT !["r11"] = registers["r11"] + 1]
        /\ pc' = "H012"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H012 == /\ pc = "H012"
        /\ registers' = [registers EXCEPT !["r12"] = registers["r12"] + 1]
        /\ pc' = "H013"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H013 == /\ pc = "H013"
        /\ registers' = [registers EXCEPT !["r13"] = registers["r13"] + 1]
        /\ pc' = "H014"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H014 == /\ pc = "H014"
        /\ registers' = [registers EXCEPT !["r14"] = registers["r14"] + 1]
        /\ pc' = "H015"
        /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, sp >>

H015 == /\ pc = "H015"
        /\ registers' = [registers EXCEPT !["r15"] = registers["r15"] + 1]
        /\ pc' = Head(stack).pc
        /\ stack' = Tail(stack)
        /\ UNCHANGED << Context, reg_, addr_, reg, addr, start_ctx, sp >>

update == H000 \/ H001 \/ H002 \/ H003 \/ H004 \/ H005 \/ H006 \/ H007
             \/ H008 \/ H009 \/ H010 \/ H011 \/ H012 \/ H013 \/ H014
             \/ H015

start_test == /\ pc = "start_test"
              /\ Context' = init_context
              /\ sp' = registers["rsp"]
              /\ registers' = [registers EXCEPT !["rdi"] = sp']
              /\ pc' = "call_save_registers"
              /\ UNCHANGED << stack, reg_, addr_, reg, addr, start_ctx >>

call_save_registers == /\ pc = "call_save_registers"
                       /\ stack' = << [ procedure |->  "save_context",
                                        pc        |->  "call_update" ] >>
                                    \o stack
                       /\ pc' = "S000"
                       /\ UNCHANGED << Context, registers, reg_, addr_, reg, 
                                       addr, start_ctx, sp >>

call_update == /\ pc = "call_update"
               /\ stack' = << [ procedure |->  "update",
                                pc        |->  "init_rsi" ] >>
                            \o stack
               /\ pc' = "H000"
               /\ UNCHANGED << Context, registers, reg_, addr_, reg, addr, 
                               start_ctx, sp >>

init_rsi == /\ pc = "init_rsi"
            /\ registers' = [registers EXCEPT !["rsi"] = sp]
            /\ pc' = "call_restore_registers"
            /\ UNCHANGED << Context, stack, reg_, addr_, reg, addr, start_ctx, 
                            sp >>

call_restore_registers == /\ pc = "call_restore_registers"
                          /\ stack' = << [ procedure |->  "restore_context",
                                           pc        |->  "end_test" ] >>
                                       \o stack
                          /\ pc' = "R000"
                          /\ UNCHANGED << Context, registers, reg_, addr_, reg, 
                                          addr, start_ctx, sp >>

end_test == /\ pc = "end_test"
            /\ Assert((callee_saved_registers = start_ctx), 
                      "Failure of assertion at line 144, column 9.")
            /\ pc' = Head(stack).pc
            /\ start_ctx' = Head(stack).start_ctx
            /\ sp' = Head(stack).sp
            /\ stack' = Tail(stack)
            /\ UNCHANGED << Context, registers, reg_, addr_, reg, addr >>

test == start_test \/ call_save_registers \/ call_update \/ init_rsi
           \/ call_restore_registers \/ end_test

check1 == /\ pc = "check1"
          /\ stack' = << [ procedure |->  "test",
                           pc        |->  "Done",
                           start_ctx |->  start_ctx,
                           sp        |->  sp ] >>
                       \o stack
          /\ start_ctx' = callee_saved_registers
          /\ sp' = defaultInitValue
          /\ pc' = "start_test"
          /\ UNCHANGED << Context, registers, reg_, addr_, reg, addr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == push \/ pop \/ save_context \/ restore_context \/ update \/ test
           \/ check1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
