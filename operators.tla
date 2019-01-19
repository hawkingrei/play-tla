----------------------------- MODULE operators -----------------------------
EXTENDS Naturals, TLC
(* --algorithm transfer
variable x \in {2, 3};

define
  add(a) == a + a
end define;  

begin
  A:
    print add(x);
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES x, pc

(* define statement *)
add(a) == a + a


vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in {2, 3}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(add(x))
     /\ pc' = "Done"
     /\ x' = x

Next == A
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Jan 19 18:13:21 CST 2019 by bilibili
\* Created Sat Jan 19 17:56:05 CST 2019 by bilibili
