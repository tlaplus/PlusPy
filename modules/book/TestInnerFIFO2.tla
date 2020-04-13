----------------------------- MODULE TestInnerFIFO2 -----------------------------
VARIABLES in, out, q

Inner == INSTANCE InnerFIFO2 WITH Message <- { "red", "blue" }

Init == Inner!Init
Next == Inner!Next
Spec == Init /\ [][Next]_<<in, out, q>>
============================================================================
