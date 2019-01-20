------------------------ MODULE dining_philosophers ------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NumPhilosophers, NULL
ASSUME NumPhilosophers > 0
NP == NumPhilosophers

(* --algorithm dining_philosophers

variables forks = [fork \in 1..NP |-> NULL]

define
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

AvailableForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}

end define;

process philosopher \in 1..NP
variables hungry = TRUE;
begin P:
  while hungry do
    either
     with fork \in AvailableForks(self) do
       forks[fork] := self;
     end with;
    or
     await AvailableForks(self) = {};
     with fork \in HeldForks(self) do
      forks[fork] := NULL;
     end with;
    end either;
    Eat:
      if Cardinality(HeldForks(self)) = 2 then
        hungry := FALSE;
        forks[LeftFork(self)] := NULL ||
        forks[RightFork(self)] := NULL;
      end if;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES forks, pc

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

AvailableForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}

VARIABLE hungry

vars == << forks, pc, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [fork \in 1..NP |-> NULL]
        (* Process philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF hungry[self]
                 THEN /\ \/ /\ \E fork \in AvailableForks(self):
                                 forks' = [forks EXCEPT ![fork] = self]
                         \/ /\ AvailableForks(self) = {}
                            /\ \E fork \in HeldForks(self):
                                 forks' = [forks EXCEPT ![fork] = NULL]
                      /\ pc' = [pc EXCEPT ![self] = "Eat"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ forks' = forks
           /\ UNCHANGED hungry

Eat(self) == /\ pc[self] = "Eat"
             /\ IF Cardinality(HeldForks(self)) = 2
                   THEN /\ hungry' = [hungry EXCEPT ![self] = FALSE]
                        /\ forks' = [forks EXCEPT ![LeftFork(self)] = NULL,
                                                  ![RightFork(self)] = NULL]
                   ELSE /\ TRUE
                        /\ UNCHANGED << forks, hungry >>
             /\ pc' = [pc EXCEPT ![self] = "P"]

philosopher(self) == P(self) \/ Eat(self)

Next == (\E self \in 1..NP: philosopher(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Jan 20 22:54:13 CST 2019 by bilibili
\* Created Sun Jan 20 22:40:41 CST 2019 by bilibili
