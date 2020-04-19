----------------------------- MODULE NBosco -----------------------------

EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Processes, Quorums, Data
ASSUME \A q \in Quorums: q \subseteq Processes
ASSUME \A q1, q2, q3 \in Quorums: q1 \intersect q2 \intersect q3 /= {}
VARIABLE procs    		\* map of processes to (round, estimate) pairs
VARIABLE inboxes        \* map of processes to received messages
VARIABLE outboxes       \* map of processes to sent messages
VARIABLE Proposals    	\* interface variable containing proposals

\* Type of vote
Vote == [ round: Nat, estimate: Data ]

\* Type of message
Message == [ src: Processes, vote: Vote ]

INFINITY == "INFINITY"

\* Extend the Less Than relation to deal with INFINITY
LT(x, y) ==
    \/ x /= INFINITY /\ y = INFINITY
    \/ x /= INFINITY /\ y /= INFINITY /\ x < y

\* Initialize the variables
Init ==
    /\ procs = [ p \in Processes |-> [ round |-> 0 ] ]
\*  /\ PrintT("INIT" \o ToString(procs))
    /\ inboxes = [ p \in Processes |-> {} ]
    /\ outboxes = [ p \in Processes |-> {} ]
    /\ Proposals = {}

\* Broadcast a message including the new state of p
Send(p) ==
    /\ outboxes' = [ outboxes EXCEPT ![p] = @ \cup
            {<<q, [ src |-> p, vote |-> procs'[p] ]>> : q \in Processes } ]
    /\ UNCHANGED <<inboxes, Proposals>>

\* From round 0, just go to round 1 and send a message
Start(p, e) ==
    /\ procs[p].round = 0
\*  /\ PrintT("GOT PROPOSAL")
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> 1, estimate |-> e ] ]
    /\ Send(p)

\* Decide if there is a unanimous quorum
Decide(p, q, e) ==
    \* If process p isn't already decided
    /\ procs[p].round /= INFINITY

    \* And all processes in q have voted e in this round
    /\ \A p2 \in q: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e ] ] \in inboxes[p]

    \* Then decide e
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> INFINITY, estimate |-> e ] ]
    /\ Send(p)

\* Proceed to the next round if there is a unanimous intersection of quorums
Maybe(p, q, e) ==
    \* If process p isn't already decided
    /\ procs[p].round /= INFINITY

    \* And all processes in q have voted in this round
    /\ \A p2 \in q: \E e2 \in Proposals: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e2 ] ] \in inboxes[p]

    \* And there exists a quorum q2 such that all processes in q*q2 have
    \* voted for e in this round
    /\ \E q2 \in Quorums: \A p2 \in q \intersect q2: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e ] ] \in inboxes[p]

    \* But the quorum is not unanimous
    /\ \E p2 \in q, e2 \in Proposals: e2 /= e /\ [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e2 ] ] \in inboxes[p]

    \* Then proceed to the next round with e
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> @.round + 1, estimate |-> e ] ]
    /\ Send(p)

Undecide(p, q, e) ==
    \* If process p isn't already decided
    /\ procs[p].round /= INFINITY

    \* And all processes in q have voted in this round
    /\ \A p2 \in q: \E e2 \in Proposals: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e2 ] ] \in inboxes[p]

    \* And some process in q voted for e in this round
    /\ \E p2 \in q: [ src |-> p2, vote |->
            [ round |-> procs[p].round, estimate |-> e ] ] \in inboxes[p]

    \* And there does not exists a quorum q2 and a value e2 such that all
    \* processes in q*q2 have voted for e2 in this round
    /\ \lnot \E q2 \in Quorums, e2 \in Proposals: \A p2 \in q \intersect q2:
            [ src |-> p2, vote |->
                [ round |-> procs[p].round, estimate |-> e2 ] ] \in inboxes[p]

    \* Then proceed to the next round with e
    /\ procs' = [ procs EXCEPT ![p] = [ round |-> @.round + 1, estimate |-> e ] ]
    /\ Send(p)

Catchup(p, m) ==
    /\ LT(procs[p].round, m.vote.round)
    /\ procs' = [ procs EXCEPT ![p] = m.vote ]
    /\ Send(p)

\* Get rid of messages no longer needed (for better output and scalability)
Cleanup(p, m) ==
    /\ LT(m.vote.round, procs[p].round)
    /\ inboxes' = [ inboxes EXCEPT ![p] = @ \ {m} ]
    /\ UNCHANGED << procs, outboxes, Proposals >>

Deliver(p, m) ==
\*  /\ PrintT("DELIVER " \o String(p) \o " " \o String(m))
    /\ inboxes' = [ inboxes EXCEPT ![p] = @ \union { m } ]
    /\ outboxes' = [ outboxes EXCEPT ![p] = @ \ { m } ]
    /\ UNCHANGED << procs, Proposals >>

Network(p) ==
    /\ \E dm \in outboxes[p]: Deliver(dm[1], dm[2])

Proc(p) ==
    \/ \E e \in Proposals: Start(p, e)
    \/ \E q \in Quorums, e \in Proposals:
        \/ Decide(p, q, e)
        \/ Maybe(p, q, e)
        \/ Undecide(p, q, e)
    \/ \E m \in inboxes[p]:
        \/ Catchup(p, m)
        \/ Cleanup(p, m)

Next == \E p \in Processes: Proc(p) \/ Network(p)

Spec == Init /\ [][Next]_<<procs, inboxes, outboxes, Proposals>>

=============================================================================
