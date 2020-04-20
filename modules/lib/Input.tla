------------------------ MODULE Input ------------------------
\* This module is an interface to get terminal input

\*++:SPEC
Receive(p, Deliver(_, _)) == \E x: Deliver(p, x)
=========================================================================

\*++:PlusPy
LOCAL INSTANCE IOUtils

Receive(p, Deliver(_, _)) ==
    /\ IOWait("fd", "stdin")
    /\ Deliver(p, IOGet("fd", "stdin"))
=========================================================================
