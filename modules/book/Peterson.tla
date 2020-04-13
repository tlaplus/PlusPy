------------------------------ MODULE Peterson ------------------------------
EXTENDS Naturals

(* --algorithm Peterson {
      variables flag = [i \in {0, 1} |-> FALSE],  turn = 0;
         \* Declares the global variables flag and turn and their initial values;
         \* flag is a 2-element array with initially flag[0] = flag[1] = FALSE.
      fair process (proc \in {0,1}) {
        \* Declares two processes with identifier self equal to 0 and 1.
        \* The keyword fair means that no process can stop forever if it can
        \* always take a step.
        a1: while (TRUE) {
             skip ;  \* the noncritical section
        a2:  flag[self] := TRUE ; 
        a3:  turn := 1 - self ; 
        a4: while (TRUE) {
              a4a: if (flag[1-self] = FALSE) {goto cs};
              a4b: if (turn = self) {goto cs}           } ;
        cs:  skip ;  \* the critical section
        a5:  flag[self] := FALSE ;
        a6:  turn := self
            }
      }
   }
*)
\* BEGIN TRANSLATION
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << flag, turn >>

a2(self) == /\ pc[self] = "a2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED turn

a3(self) == /\ pc[self] = "a3"
            /\ turn' = 1 - self
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED flag

a4(self) == /\ pc[self] = "a4"
            /\ pc' = [pc EXCEPT ![self] = "a4a"]
            /\ UNCHANGED << flag, turn >>

a4a(self) == /\ pc[self] = "a4a"
             /\ IF flag[1-self] = FALSE
                   THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "a4b"]
             /\ UNCHANGED << flag, turn >>

a4b(self) == /\ pc[self] = "a4b"
             /\ IF turn = self
                   THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "a4"]
             /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << flag, turn >>

a5(self) == /\ pc[self] = "a5"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a6"]
            /\ UNCHANGED turn

a6(self) == /\ pc[self] = "a6"
            /\ turn' = self
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED flag

proc(self) == a1(self) \/ a2(self) \/ a3(self) \/ a4(self) \/ a4a(self)
                 \/ a4b(self) \/ cs(self) \/ a5(self) \/ a6(self)

Next == (\E self \in {0,1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

\* END TRANSLATION

THEOREM Spec => [] (pc[0] /= "cs") \/ (pc[1] /= "cs")

THEOREM Spec => \A i \in {0,1} : []<>(pc[i] = "cs")

=============================================================================
\* Modification History
\* Last modified Sat Mar 14 05:47:06 EDT 2020 by rvr
\* Created Sat Feb 29 21:49:27 EST 2020 by rvr
