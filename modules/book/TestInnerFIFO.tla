----------------------------- MODULE TestInnerFIFO -----------------------------
VARIABLES in, out, q

Inner == INSTANCE InnerFIFO WITH Message <- { "red", "blue" }

Init == Inner!Init
Next == Inner!Next
Spec == Init /\ [][Next]_<<in, out, q>>
============================================================================
