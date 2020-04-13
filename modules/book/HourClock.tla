----------------------------- MODULE HourClock -----------------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1..12)
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
HC == HCini /\ [][HCnxt]_hr

(* Added for simplicity of pluspy testing *)
Init == HCini
Next == HCnxt
Spec == HC

=============================================================================
\* Modification History
\* Last modified Sat Feb 01 19:29:17 EST 2020 by rvr
\* Created Sat Feb 01 19:26:43 EST 2020 by rvr
