----------------------------- MODULE TestChannel -----------------------------
VARIABLE chan
C == INSTANCE Channel WITH Data <- { "red", "blue" }

Init == C!Init
Next == C!Next
Spec == Init /\ [][Next]_<<chan>>
============================================================================
