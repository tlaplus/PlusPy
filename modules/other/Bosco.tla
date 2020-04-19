----------------------------- MODULE Bosco -----------------------------

EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Processes, Quorums, Data
ASSUME \A q \in Quorums: q \subseteq Processes
ASSUME \A q1, q2, q3 \in Quorums: q1 \intersect q2 \intersect q3 /= {}
VARIABLE procs    		\* map of processes to (round, estimate) pairs
VARIABLE msgs           \* map of processes to received messages
VARIABLE mi             \* messaging interface

\* Type of vote
Vote == [ round: Nat, estimate: Data ]

\* Type of message
Message == [ src: Processes, vote: Vote ]

Network == INSTANCE Messaging
Stdin   == INSTANCE Input

INFINITY == "INFINITY"

\* Extend the Less Than relation to deal with INFINITY
LT(x, y) ==
    \/ x /= INFINITY /\ y = INFINITY
    \/ x /= INFINITY /\ y /= INFINITY /\ x < y

\* Initialize the variables
Init ==
    /\ procs = [ p \in Processes |-> [ round |-> 0 ] ]
    /\ msgs = [ p \in Processes |-> {} ]
    /\ Network!Init
    /\ Print("Enter a proposal: ", TRUE)

\* Broadcast a message including the new state of p
Send(p) ==
    /\ Network!Send(
        {<<q, [ src |-> p, vote |-> procs'[p] ]>> : q \in Processes })
    /\ UNCHANGED <<msgs>>

\* From round 0, just go to round 1 and send a message
Start(p, e) ==
    /\ procs[p].round = 0
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> 1, estimate |-> e ] ]
    /\ Send(p)

\* Decide if there is a unanimous quorum
Decide(p, q, e) ==
    \* If process p isn't already decided
    /\ procs[p].round /= INFINITY

    \* And all processes in q have voted e in this round
    /\ \A p2 \in q: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e ] ] \in msgs[p]

    \* Then decide e
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> INFINITY, estimate |-> e ] ]
    /\ Send(p)

\* Proceed to the next round if there is a unanimous intersection of quorums
Maybe(p, q, e) ==
    \* If process p isn't already decided
    /\ procs[p].round /= INFINITY

    \* And all processes in q have voted in this round
    /\ \A p2 \in q: \E e2 \in Data: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e2 ] ] \in msgs[p]

    \* And there exists a quorum q2 such that all processes in q*q2 have
    \* voted for e in this round
    /\ \E q2 \in Quorums: \A p2 \in q \intersect q2: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e ] ] \in msgs[p]

    \* But the quorum is not unanimous
    /\ \E p2 \in q, e2 \in Data: e2 /= e /\ [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e2 ] ] \in msgs[p]

    \* Then proceed to the next round with e
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> @.round + 1, estimate |-> e ] ]
    /\ Send(p)

Undecide(p, q, e) ==
    \* If process p isn't already decided
    /\ procs[p].round /= INFINITY

    \* And all processes in q have voted in this round
    /\ \A p2 \in q: \E e2 \in Data: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e2 ] ] \in msgs[p]

    \* And some process in q voted for e in this round
    /\ \E p2 \in q: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e ] ] \in msgs[p]

    \* And there does not exists a quorum q2 and a value e2 such that all
    \* processes in q*q2 have voted for e2 in this round
    /\ \lnot \E q2 \in Quorums, e2 \in Data: \A p2 \in q \intersect q2:
            [ src |-> p2, vote |->
                [ round |-> procs[p].round, estimate |-> e2 ] ] \in msgs[p]

    \* Then proceed to the next round with e
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> @.round + 1, estimate |-> e ] ]
    /\ Send(p)

\* Get rid of messages no longer needed (for better output and scalability)
Cleanup(p, m) ==
    /\ LT(m.vote.round, procs[p].round)
    /\ msgs' = [ msgs EXCEPT ![p] = @ \ {m} ]
    /\ UNCHANGED << procs, mi >>

Deliver(p, m) ==
    /\ msgs' = [ msgs EXCEPT ![p] = @ \union { m } ]
    /\ UNCHANGED << procs >>

Proc(p) ==
    \/ Network!Receive(p, Deliver)
    \/ Stdin!Receive(p, Start)
    \/ \E q \in Quorums, e \in Data:
        \/ Decide(p, q, e)
        \/ Maybe(p, q, e)
        \/ Undecide(p, q, e)
    \/ \E m \in msgs[p]:
        \/ Cleanup(p, m)

Next == \E p \in Processes: Proc(p)

Spec == Init /\ [][Next]_<<procs, msgs, mi>>

=============================================================================
