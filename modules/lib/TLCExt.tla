------------------------------- MODULE TLCExt ----------------------------------
\* This module provides some compatibility with the TLC module

LOCAL INSTANCE Naturals
LOCAL INSTANCE IOUtils
-----------------------------------------------------------------------------

ToString(v) == (CHOOSE x \in [a : v, b : STRING] : TRUE).b
Print(out, val) == IF IOPut("fd", "stdout", out) THEN val ELSE val
PrintT(out) == Print(out, TRUE)

Any == CHOOSE x : x \notin { "Any" }

JSignalReturn(t, d) == d
    /\ IOPut("local", t, d)
JReturn(d) == d
JWait(t) ==
    /\ IOWait("local", t)
    /\ IOGet("local", t) \notin {}
=============================================================================
