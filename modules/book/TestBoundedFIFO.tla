----------------------------- MODULE TestBoundedFIFO -----------------------------
VARIABLES in, out

Inner == INSTANCE BoundedFIFO WITH Message <- { "red", "blue" }, N <- 2

Spec == Inner!Spec
============================================================================
