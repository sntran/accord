------------------------------- MODULE Lock -------------------------------
(* A lock for a set of clients. The test of Accord.Spec monitors a       *)
(* GenServer against this module, and the model checker checks it.      *)
EXTENDS Naturals

CONSTANT Clients

VARIABLES holder, grants

NoOne == "none"

Init == holder = NoOne /\ grants = 0

\* A client asks for the lock. The reply r is "ok" or "busy".
Acquire(c, r) ==
    \/ /\ holder = NoOne
       /\ r = "ok"
       /\ holder' = c
       /\ grants' = grants + 1
    \/ /\ holder # NoOne
       /\ r = "busy"
       /\ UNCHANGED <<holder, grants>>

\* The holder gives the lock back.
Release(c, r) ==
    /\ holder = c
    /\ r = "ok"
    /\ holder' = NoOne
    /\ UNCHANGED grants

\* The server tells the holder that it has the lock.
Granted(c) == holder = c /\ UNCHANGED <<holder, grants>>

Next == \E c \in Clients, r \in {"ok", "busy"} :
            Acquire(c, r) \/ Release(c, r) \/ Granted(c)

TypeOK == holder \in Clients \cup {NoOne} /\ grants \in Nat

Bounded == grants =< 2
=============================================================================
