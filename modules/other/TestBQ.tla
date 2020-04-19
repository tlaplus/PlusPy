------------------------- MODULE TestBQ -------------------------
VARIABLES buffer, waitSetC, waitSetP

Producers == { "p1", "p2", "p3" }
Consumers == { "c1", "c2", "c3" }

BQ == INSTANCE BlockingQueueSplit WITH BufCapacity <- 3

producer(p) == BQ!Put(p, p)
consumer(c) == BQ!Get(c)

Init == BQ!Init
Next == \/ \E p \in Producers: producer(p)
        \/ \E c \in Consumers: consumer(c)

Spec == Init /\ [][Next]_<<buffer, waitSetC, waitSetP>>
=============================================================================
