---------------------------- MODULE hello_world ----------------------------
EXTENDS Naturals, TLC
(* --algorithm transfer
variable s \in {"Hello", "World!"}, x \in {2, 3};
begin
  A:
    print s;
  B:
    if x = 5 then
      skip;
    elsif x = 6 then
      skip;
    else
      skip;
    end if;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES s, x, pc

vars == << s, x, pc >>

Init == (* Global variables *)
        /\ s \in {"Hello", "World!"}
        /\ x \in {2, 3}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(s)
     /\ pc' = "B"
     /\ UNCHANGED << s, x >>

B == /\ pc = "B"
     /\ IF x = 5
           THEN /\ TRUE
           ELSE /\ IF x = 6
                      THEN /\ TRUE
                      ELSE /\ TRUE
     /\ pc' = "Done"
     /\ UNCHANGED << s, x >>

Next == A \/ B
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Jan 19 16:05:38 CST 2019 by bilibili
\* Created Sat Jan 19 15:15:54 CST 2019 by bilibili
