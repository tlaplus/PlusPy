----------------------------- MODULE TestBinBosco -----------------------------
EXTENDS Naturals
VARIABLES processes, mi, msgs

Processes ==
    {
        "localhost:5001", "localhost:5002", "localhost:5003", "localhost:5004"
    }

Inputs ==
    [ [ p \in Processes |-> "" ] EXCEPT
        !["localhost:5001"] = "red",
        !["localhost:5002"] = "blue",
        !["localhost:5003"] = "red",
        !["localhost:5004"] = "blue"
    ]

BB == INSTANCE BinBosco WITH
    Processes <- Processes,
    Quorums <- { Processes \ {p}: p \in Processes },
    Data    <- { "red", "blue" },
    procs   <- processes

Init == BB!Init
Next == BB!Next
Proc(p) == BB!Proc(p)
Spec == Init /\ [][Next]_<<processes, msgs>>
============================================================================
