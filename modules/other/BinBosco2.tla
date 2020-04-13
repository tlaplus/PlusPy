----------------------------- MODULE BinBosco2 -----------------------------

EXTENDS Naturals, FiniteSets
(* See below...
	CONSTANTS Processes, Quorums, Data, Inputs
	ASSUME \A q \in Quorums: q \subseteq Processes
	ASSUME \A q1, q2, q3 \in Quorums: q1 \intersect q2 \intersect q3 /= {}
	ASSUME Inputs \in [Processes -> Data ]
	ASSUME Cardinality(Data) \in { 1, 2 }
*)
VARIABLE mystate, Messages

(* TODO.  Use "INSTANCE" to do this *)
Processes == { 0, 1, 2, 3 }
Quorums == { { 0, 1, 2 }, { 0, 1, 3 }, { 0, 2, 3 }, { 1, 2, 3 } }
Data == { "red", "blue" }
Inputs == << "red", "blue", "red", "blue" >>

Init ==
    /\ mystate = [ round |-> 0, estimate |-> 0 ]
    /\ Messages = {}

Start(p) ==
    /\ mystate.round = 0
    /\ mystate' = [ round |-> 1, estimate |-> Inputs[p] ]
    /\ Messages' = Messages \union { [ src |-> p, vote |-> mystate' ] }

Step(p, q1, q2, e) ==
    /\ \A p2 \in q1 \intersect q2: [ src |-> p2, vote |-> [ round |-> mystate.round, estimate |-> e ] ] \in Messages
    /\ mystate' = [ round |-> mystate.round + 1, estimate |-> e ]
    /\ Messages' = Messages \union { [ src |-> p, vote |-> mystate' ] }

Catchup(p, m) ==
    /\ m.vote.round > mystate.round
    /\ mystate' = m.vote
    /\ Messages' = Messages \union { [ src |-> p, vote |-> mystate' ] }

Proc(p) ==
    \/ Start(p)
    \/ \E q1, q2 \in Quorums, e \in Data: Step(p, q1, q2, e)
    \/ \E m \in Messages: Catchup(p, m)

Next == \E p \in Processes: Proc(p)

Spec == Init /\ [][Next]_<<procs, Messages>>

=============================================================================
