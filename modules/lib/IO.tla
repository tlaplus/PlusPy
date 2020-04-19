------------------------------- MODULE IO ----------------------------------
\* This module essentially uses a hidden sequence variable H

\* Append << intf, mux, data >> to the end of sequence H
IOPut(intf, mux, data) == TRUE \* H' = Append(H, <<intf, mux, data>>)

\* Wait until there is an element of the form <<intf, mux, _>> in sequence H
IOWait(intf, mux) == TRUE \* \E i \in Nat, d \in Data: H[i] = <<intf, mux, d>>

\* Remove the first element of the form <<intf, mux, data>> from sequence H
\* and return data
IOGet(intf, mux) == TRUE \* hard to formalize...
=============================================================================
