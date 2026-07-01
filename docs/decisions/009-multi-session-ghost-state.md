# ADR-009: Multi-session model checking with ghost shared state

## Status

Accepted (qualifies ADR-002)

## Context

The generated TLA+ model had one scalar `state` variable: one session. But the interesting
safety claims of protocols like the fencing-token lock are *cross-session* — no two clients hold
the lock at once, no job is processed twice. Those bugs live in the interleaving of sessions,
which a single-session model structurally cannot represent. TLC could never find them.

Making cross-session state real at *runtime* would require a store shared across monitor
instances (ETS or a coordinator process) with its own serialization semantics — effectively a
second server whose consistency with the real server is itself unverifiable. The server *is* the
ground truth for shared state; duplicating it at runtime buys little and costs a distributed-
systems problem.

## Decision

**Shared tracks and multi-session checking are ghost state: verified by TLC, not enforced at
runtime.**

- `track ..., shared: true` marks state that lives on the server and is observed by every
  session. In the model it is a single scalar variable all session actions read and write.
- `sessions: N` in the model config makes per-session variables functions `[Sessions -> Domain]`
  and existentially quantifies the acting session in every action. `sessions: 1` (default)
  leaves emission unchanged.
- `exclusive :state` declares cross-session mutual exclusion — a real TLC invariant at
  `sessions >= 2`, an honest annotation otherwise.
- The runtime monitor is unchanged: one instance per session, each keeping its own copy of every
  track updated only by its session's traffic.

The asymmetry is stated loudly rather than hidden:

- W003 warns when shared tracks or exclusive checks are declared but `sessions: 1`.
- The architecture documentation carries a "what the runtime checks vs. what TLC checks" table.
- Runtime checking of shared-track properties is *weaker* than the model: a server issuing
  non-monotonic fence tokens across two clients passes each monitor individually but fails TLC.

## Consequences

- TLC finds the concurrency bugs the project was named for: the unguarded distributed-lock
  fixture yields the two-sessions-both-locked counterexample in three states, with fence tokens
  still monotonic — fencing alone is not a lock.
- ADR-002's "the model checks exactly what the monitor enforces" is now qualified: the model
  checks *at least* what the monitor enforces, plus cross-session properties the monitor
  cannot see. The divergence is declared per-construct, never silent.
- Local invariants change meaning under shared tracks: `invariant :unlocked, fn _,
  t -> t.holder == nil end` quantifies over ALL sessions in `:unlocked`, so it is wrong for a
  multi-session lock (one session being unlocked while another holds is intended). Protocol
  authors write cross-session properties with `exclusive` and shared-track invariants instead.
- Symmetry over `Sessions` is applied automatically (a large state-space reduction), suppressed
  when liveness properties are present because TLC's symmetry reduction is unsound for them.
