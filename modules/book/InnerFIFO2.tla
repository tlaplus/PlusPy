---------------------------- MODULE InnerFIFO2 -------------------------------
EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out, q
MyChan(c)  == INSTANCE Channel WITH Data <- Message, chan <- c
-----------------------------------------------------------------------------
Init == /\ MyChan(in)!Init
        /\ MyChan(out)!Init
        /\ q = << >>

TypeInvariant  ==  /\ MyChan(in)!TypeInvariant
                   /\ MyChan(out)!TypeInvariant
                   (*RVR /\ q \in Seq(Message) *)

SSend(msg)  ==  /\ MyChan(in)!Send(msg) \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>

BufRcv == /\ MyChan(in)!Rcv              \* Receive message from channel `in'.
          /\ q' = Append(q, in.val)  \*   and append it to tail of q.
          /\ UNCHANGED out

BufSend == /\ q # << >>               \* Enabled only if q is nonempty.
           /\ MyChan(out)!Send(Head(q))   \* Send Head(q) on channel `out'
           /\ q' = Tail(q)            \*   and remove it from q.
           /\ UNCHANGED in

RRcv == /\ MyChan(out)!Rcv          \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv 

Spec == Init /\ [][Next]_<<in, out, q>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
TypeInvariant == TRUE
=============================================================================
