----------------------------- MODULE BinBosco -----------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Processes, Inputs, Quorums, Data

ASSUME \A q \in Quorums: q \subseteq Processes
ASSUME \A q1, q2, q3 \in Quorums: q1 \intersect q2 \intersect q3 /= {}
ASSUME Cardinality(Data) \in { 1, 2 }

VARIABLES procs, mi, msgs

\* Type of vote
Vote == [ round: Nat, estimate: Data ]

\* Type of message
Message == [ src: Processes, vote: Vote ]

Network == INSTANCE Messaging

Init ==
    /\ procs = [ p \in Processes |-> [ round |-> 0, estimate |-> Inputs[p] ] ]
    /\ msgs = [ p \in Processes |-> {} ]
    /\ Network!Init

Start(p) ==
    /\ procs[p].round = 0
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> 1, estimate |-> procs[p].estimate ] ]
    /\ Network!Send(
        {<<q, [ src |-> p, vote |-> procs'[p] ]>> : q \in Processes })
    /\ UNCHANGED msgs

Step(p, q1, q2, e) ==
    /\ procs[p].round < 5		(* useful for testing *)
    /\ \A p2 \in q1 \intersect q2: [ src |-> p2, vote |-> [ round |-> procs[p].round, estimate |-> e ] ] \in msgs[p]
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> procs[p].round + 1, estimate |-> e ] ]
    /\ Network!Send(
        {<<q, [ src |-> p, vote |-> procs'[p] ]>> : q \in Processes })
    /\ UNCHANGED msgs

\* Get rid of messages no longer needed (for better output and scalability)
Cleanup(p, m) ==
    /\ m.vote.round < procs[p].round
    /\ msgs' = [ msgs EXCEPT ![p] = @ \ {m} ]
    /\ UNCHANGED <<procs, mi>>

Catchup(p, m) ==
    /\ m.vote.round > procs[p].round
    /\ procs' = [ procs EXCEPT ![p] = m.vote ]
    /\ Network!Send(
        {<<q, [ src |-> p, vote |-> procs'[p] ]>> : q \in Processes })
    /\ UNCHANGED msgs

Deliver(p, m) ==
\*  /\ PrintT("DELIVER " \o ToString(p) \o " " \o ToString(m))
    /\ msgs' = [ msgs EXCEPT ![p] = @ \union { m } ]
    /\ UNCHANGED procs

Proc(p) ==
    \/ Start(p)
    \/ \E q1, q2 \in Quorums, e \in Data: Step(p, q1, q2, e)
    \/ Network!Receive(p, Deliver)
    \/ \E m \in msgs[p]: (Cleanup(p, m) \/ Catchup(p, m))

Next == \E p \in Processes: Proc(p)

Spec == Init /\ [][Next]_<<procs, mi>>

=============================================================================
