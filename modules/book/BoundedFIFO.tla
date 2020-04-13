-------------------- MODULE BoundedFIFO ---------------------
EXTENDS Naturals, Sequences
VARIABLES in, out
CONSTANT Message, N
ASSUME (N \in Nat) /\ (N > 0)
Inner(q) == INSTANCE InnerFIFO 
BNext(q) == /\ Inner(q)!Next
            /\ Inner(q)!BufRcv => (Len(q) < N)

Spec == \EE q: Inner(q)!Init /\ [][BNext(q)]_<<in, out, q>>
=============================================================
