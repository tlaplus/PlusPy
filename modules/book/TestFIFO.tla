----------------------------- MODULE TestFIFO -----------------------------
VARIABLES in, out

Inner == INSTANCE FIFO WITH Message <- { "red", "blue" }

Spec == Inner!Spec
============================================================================
