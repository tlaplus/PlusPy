------------------------------- MODULE Prime -------------------------------
EXTENDS Naturals, Sequences
VARIABLE count, p

isPrime(x) == x > 1 /\ \A r \in 2..(x-1): x%r /= 0

TypeInvariant == isPrime(p) /\ count \in Nat

Init == p = 2 /\ count = 1
Next == /\ p' = CHOOSE q \in (p+1)..(2*p-1):
               isPrime(q) /\ \A r \in (p+1)..(q-1): ~isPrime(r)
        /\ count' = count + 1

Spec == Init /\ [] [Next]_<<p, count>>

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Mon Jan 27 14:20:50 EST 2020 by rvr
\* Created Mon Jan 27 14:05:36 EST 2020 by rvr
