------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE chan

TypeInvariant == chan \in [ val: Data, rdy: {0, 1}, ack: {0, 1} ]

-----------------------------------------------------------------------------

(* RVR
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy
*)
Init == \E d \in Data, v \in 0..1: chan = [ val |-> d, rdy |-> v, ack |-> v ]

Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv == /\ chan.rdy /= chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]
       
Next == (\E x \in Data: Send(x)) \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Thu Mar 19 08:54:34 EDT 2020 by rvr
\* Created Sun Feb 02 14:35:33 EST 2020 by rvr
