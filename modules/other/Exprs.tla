----------------------------- MODULE Exprs -----------------------------
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]
fact2[n \in 0..4] == IF n = 0 THEN 1 ELSE n * fact2[n - 1]

Tests ==
    <<
        << FALSE /\ FALSE, FALSE >>,
        << FALSE /\ TRUE, FALSE >>,
        << TRUE /\ FALSE, FALSE >>,
        << TRUE /\ TRUE, TRUE >>,

        << FALSE \/ FALSE, FALSE >>,
        << FALSE \/ TRUE, TRUE >>,
        << TRUE \/ FALSE, TRUE >>,
        << TRUE \/ TRUE, TRUE >>,

        << FALSE => FALSE, TRUE >>,
        << FALSE => TRUE, TRUE >>,
        << TRUE => FALSE, FALSE >>,
        << TRUE => TRUE, TRUE >>,

        << FALSE <=> FALSE, TRUE >>,
        << FALSE <=> TRUE, FALSE >>,
        << TRUE <=> FALSE, FALSE >>,
        << TRUE <=> TRUE, TRUE >>,

        << FALSE \equiv FALSE, TRUE >>,
        << FALSE \equiv TRUE, FALSE >>,
        << TRUE \equiv FALSE, FALSE >>,
        << TRUE \equiv TRUE, TRUE >>,

        << ~TRUE, FALSE >>,
        << ~FALSE, TRUE >>,
        << \lnot TRUE, FALSE >>,
        << \lnot FALSE, TRUE >>,
        << \neg TRUE, FALSE >>,
        << \neg FALSE, TRUE >>,
        << ~TRUE \/ TRUE, TRUE >>,
        << ~(TRUE \/ TRUE), FALSE >>,

        << 1 \in 1..2, TRUE >>,
        << 1 \in 2..2, FALSE >>,
        << 1 \notin 1..2, FALSE >>,
        << 1 \notin 2..2, TRUE >>,

        << 1 = 1, TRUE >>,
        << 1 = 2, FALSE >>,
        << 1 /= 1, FALSE >>,
        << 1 /= 2, TRUE >>,
        << 1 # 1, FALSE >>,
        << 1 # 2, TRUE >>,

        << SUBSET {}, {{}} >>,
        << SUBSET {1}, {{}, {1}} >>,
        << SUBSET {1, 2}, {{}, {1}, {2}, {1, 2}} >>,

        << UNION {}, {} >>,
        << UNION {{}}, {} >>,
        << UNION {{1}}, {1} >>,
        << UNION {{1},{2}}, {1, 2} >>,

        << { 1 } \subset { }, FALSE >>,
        << { 1 } \subset { 1 }, FALSE >>,
        << { 1 } \subset { 2 }, FALSE >>,
        << { 1 } \subset { 1, 2 }, TRUE >>,
        << { 1 } \subseteq { }, FALSE >>,
        << { 1 } \subseteq { 1 }, TRUE >>,
        << { 1 } \subseteq { 2 }, FALSE >>,
        << { 1 } \subseteq { 1, 2 }, TRUE >>,

        << { } \supset { 1 }, FALSE >>,
        << { 1 } \supset { 1 }, FALSE >>,
        << { 2 } \supset { 1 }, FALSE >>,
        << { 1, 2 } \supset { 1 }, TRUE >>,
        << { } \supseteq { 1 }, FALSE >>,
        << { 1 } \supseteq { 1 }, TRUE >>,
        << { 2 } \supseteq { 1 }, FALSE >>,
        << { 1, 2 } \supseteq { 1 }, TRUE >>,

        << { 1, 2 } \union { 2, 3 }, { 1, 2, 3} >>,
        << { 1, 2 } \cup { 2, 3 }, { 1, 2, 3} >>,
        << { 1, 2 } \intersect { 2, 3 }, { 2 } >>,
        << { 1, 2 } \cap { 2, 3 }, { 2 } >>,
        << { 1, 2 } \ { 2, 3 }, { 1 } >>,

        << 1 + 2, 3 >>,
        << -. 3, -3 >>,
        << - (1 + 2), -3 >>,
        << - (1 + 2) + 4, 1 >>,
        << 1 + 2 * 3, 7 >>,
        << 1 * 2 + 3, 5 >>,
        << 1..2, { 1, 2 } >>,
        << 1..-2, {} >>,
        << 8 \div 4, 2 >>,
        << 5 % 4, 1 >>,
        << 2^3, 8 >>,

        << 1 < 1, FALSE >>,
        << 1 < 2, TRUE >>,
        << 1 <= 0, FALSE >>,
        << 1 <= 1, TRUE >>,
        << 1 =< 0, FALSE >>,
        << 1 =< 1, TRUE >>,
        << 1 \leq 0, FALSE >>,
        << 1 \leq 1, TRUE >>,
        << 1 > 1, FALSE >>,
        << 1 > 0, TRUE >>,
        << 1 >= 1, TRUE >>,
        << 1 >= 2, FALSE >>,
        << 1 \geq 1, TRUE >>,
        << 1 \geq 2, FALSE >>,

        << (1..2) \X (3..4), { << 1, 3 >>, << 1, 4 >>,
                                << 2, 3 >>, << 2, 4 >> } >>,
        << (1..2) \times (3..4), { << 1, 3 >>, << 1, 4 >>,
                                << 2, 3 >>, << 2, 4 >> } >>,
        << (1..2) \X (3..4) \X (5..6), { << 1, 3, 5 >>, << 1, 3, 6 >>,
                << 1, 4, 5 >>, << 1, 4, 6 >>, << 2, 3, 5 >>,
                << 2, 3, 6 >>, << 2, 4, 5 >>, << 2, 4, 6 >> } >>,

        << << 2 >>[1], 2 >>,
        << << "a", "b", "c" >>[2], "b" >>,
        << Len(<< 1, 1, 1 >>), 3 >>,
        << Head(<< 1, 2, 3 >>), 1 >>,
        << Tail(<< 1, 2, 3 >>), << 2, 3 >> >>,
        << Append(<< 1, 2 >>, 3), << 1, 2, 3 >> >>,
        << << 1 >> \o << 2, 3 >>, << 1, 2, 3 >> >>,
        << SubSeq(<< 1, 2, 3 >>, 1, 2), << 1, 2 >> >>,
        << SelectSeq(<< FALSE, TRUE >>, ~), << FALSE >> >>,
        << SortSeq(<< >>, <), << >> >>,
        << SortSeq(<< 3, 1, 2 >>, <), << 1, 2, 3 >> >>,
        << SortSeq(<< 3, 1, 2 >>, >), << 3, 2, 1 >> >>,

        << "", <<>> >>,
        << DOMAIN "", {} >>,
        << DOMAIN "abc", 1..3 >>,
        << "a", << "a"[1] >> >>,
        << "a" \o "b", "ab" >>,
        << [ "ab" EXCEPT ![1] = "b"[1] ], "bb" >>,
        << [ "ab" EXCEPT ![1] = 1 ], << 1, "b"[1] >> >>,
        << SubSeq("Hello", 2, 4), "ell" >>,
        << Len("hello"), 5 >>,

        << { 1, 1, 1 }, { 1 } >>,
        << Cardinality({}), 0 >>,
        << Cardinality({ "a", "b", "c" }), 3 >>,

        << { x \in 1..5: x % 2 = 0 }, { 2, 4 } >>,
        << { 2*x: x \in 1..3 }, { 2, 4, 6 } >>,
        << [ a: 1..2, b:3..4 ], { [ a |-> 1, b |-> 3 ],
                [ a |-> 1, b |-> 4 ], [ a |-> 2, b |-> 3 ],
                [ a |-> 2, b |-> 4 ] } >>,
        << [ x \in 1..2 |-> 3 ], << 3, 3 >> >>,
        << [ x \in { "a", "b" } |-> 3 ], [ a |-> 3, b |-> 3 ] >>,

        << \E x \in 1..5: x <= 1, TRUE >>,
        << \E x \in 1..5: x <= 0, FALSE >>,
        << \A x \in 1..5: x <= 5, TRUE >>,
        << \A x \in 1..5: x <= 4, FALSE >>,

        << IF FALSE THEN 1 ELSE 2, 2 >>,
        << IF TRUE THEN 1 ELSE 2, 1 >>,
        << CASE FALSE -> 1 [] TRUE -> 2, 2 >>,
        << CASE TRUE -> 1 [] FALSE -> 2, 1 >>,
        << CASE FALSE -> 1 [] OTHER -> 2, 2 >>,
        << CASE TRUE -> 1 [] OTHER -> 2, 1 >>,
 
        << LET x == 3 IN 2*x, 6 >>,
        << LET d(x) == 2*x IN d(3), 6 >>,
        << CHOOSE x: x = 3, 3 >>,
        << CHOOSE x: x \in { 3 }, 3 >>,
        << CHOOSE x \in 1..5: x = 3, 3 >>,
        << CHOOSE x \in 1..5: x > 2 /\ x < 4, 3 >>,

        << SetToBag(1..3), << 1, 1, 1 >> >>,
        << SetToBag(1..3) (+) SetToBag(2..4), << 1, 2, 2, 1 >> >>,
        << BagToSet(SetToBag(1..3) (+) SetToBag(2..4)), 1..4 >>,
        << BagIn(2, SetToBag(1..3)), TRUE >>,
        << BagIn(0, SetToBag(1..3)), FALSE >>,
        << EmptyBag, <<>> >>,
        << CopiesIn(1, SetToBag(1..3) (+) SetToBag(2..4)), 1 >>,
        << CopiesIn(3, SetToBag(1..3) (+) SetToBag(2..4)), 2 >>,
        << CopiesIn(5, SetToBag(1..3) (+) SetToBag(2..4)), 0 >>,

        << fact[0], 1 >>,
        << fact[4], 24 >>,
        << fact2[0], 1 >>,
        << fact2[4], 24 >>,
        << fact2, [ i \in 0..4 |-> fact[i] ] >>,
        << CHOOSE f: f = [ n \in 0..4 |->
                IF n = 0 THEN 1 ELSE n * f[n-1] ], fact2 >>,

        << 0, 0 >>
    >>

Incorrect(test) == test[1] /= test[2]

\* TODO.  Come up with expression that says which tests failed
Failed == SelectSeq(Tests, Incorrect)

Init == PrintT(ToString(Failed)) /\ (Failed = <<>>)
Next == TRUE

Spec == Init /\ [][Next]_<<>>
=======================================================================
