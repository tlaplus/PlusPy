---- MODULE Naturals ----
EXTENDS Core

Nat == CHOOSE x: x \notin {"Nat"}

s - t == FALSE
s < t == FALSE
s > t == FALSE
s >= t == FALSE
s \geq t == FALSE
s <= t == FALSE
s =< t == FALSE
s \leq t == FALSE
s + t == FALSE
s * t == FALSE
s / t == FALSE
s \div t == FALSE
s % t == FALSE
s ^ t == FALSE

s .. t == FALSE
===============================
