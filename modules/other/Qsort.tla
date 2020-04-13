----------------------------- MODULE Qsort -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* CONSTANT input
input == << 0, 383, 886, 777, 915, 793, 335, 386, 492, 649, 421, 362, 27, 690, 59, 763, 926, 540, 426, 172, 736, 211, 368, 567, 429, 782, 530, 862, 123, 67, 135, 929, 802, 22, 58, 69, 167, 393, 456, 11, 42, 229, 373 >>

VARIABLES todo, output

\* Specification (works reasonably well for sets of cardinality <= 6
\* Takes a set as argument, produces a sorted tuple
Sort(S) == CHOOSE s \in [ 1..Cardinality(S) -> S]:
    \A i, j \in DOMAIN s: (i < j) => (s[i] < s[j])

Flatten[s \in Seq(Seq(Nat))] ==
    IF s = <<>> THEN <<>>
    ELSE Head(s) \o Flatten[Tail(s)]

Partition(s) ==
    LET LE(x) == x <= Head(s)
        GT(x) == x > Head(s)
    IN << SelectSeq(Tail(s), LE), << Head(s) >>, SelectSeq(Tail(s), GT) >>

Init == todo = << input >> /\ output = "under construction"
Next ==
    IF \E i \in 1..Len(todo): Len(todo[i]) > 1 /\
        todo' = SubSeq(todo, 1, i-1) \o Partition(todo[i]) \o
                            SubSeq(todo, i+1, Len(todo))
    THEN UNCHANGED output
    ELSE output' = Flatten[todo] /\ UNCHANGED todo

Spec == Init /\ [][Next]_<<todo, output>>
=============================================================================
