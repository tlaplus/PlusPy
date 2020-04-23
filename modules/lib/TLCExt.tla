------------------------------- MODULE TLCExt ----------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE IOUtils
-----------------------------------------------------------------------------
JSignalReturn(t, d) == d
    /\ IOPut("local", t, d)
JReturn(d) == d
JWait(t) ==
    /\ IOWait("local", t)
    /\ IOGet("local", t) \notin {}
=============================================================================
