----------------------------- MODULE TestBosco -----------------------------
EXTENDS Naturals
VARIABLES processes, Proposals, mi, msgs

B == INSTANCE Bosco WITH
    Processes <- 1..4,
    Quorums   <- { { 1, 2, 3 }, { 1, 2, 4 }, { 1, 3, 4 }, { 2, 3, 4 } },
    procs     <- processes

Init == B!Init
Next == B!Next
Proc(p) == B!Proc(p)
Spec == Init /\ [][Next]_<<processes, mi, msgs, Proposals>>
============================================================================
