------------ MODULE Core ------------

STRING == CHOOSE x: x \notin {"STRING"}

(*
    s /\ t == FALSE
    s \/ t == FALSE
    s = t == FALSE
    s \in t == FALSE
    s \notin t == FALSE
*)

s <=> t == FALSE
s \equiv t == FALSE
s # t == FALSE
s /= t == FALSE

s \subset t == FALSE
s \subseteq t == FALSE
s \supset t == FALSE
s \supseteq t == FALSE
s \ t == FALSE
s \cap t == FALSE
s \intersect t == FALSE
s \cup t == FALSE
s \union t == FALSE

DOMAIN s == FALSE
UNION s == FALSE
SUBSET s == FALSE
~ s == FALSE
\lnot s == FALSE
\neg s == FALSE

s => t == (~s) \/ t

=========================================
