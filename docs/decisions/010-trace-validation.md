# ADR-010: Trace validation

## Status

Accepted

## Context

Every other check has a blind spot around accord's own TLA+ compiler. TLC checks the generated
model against itself — if `BuildActions` mistranslates a guard or drops an update, TLC happily
verifies the wrong protocol. The property-based exerciser drives real servers through the
monitor but never consults the model. Nothing connected what *actually happens* at runtime to
what the spec *says* can happen.

## Decision

**Capture runtime traces and require the spec to accept them as behaviors.**

- A monitor started with `trace_sink:` emits one `Accord.Trace.Event` per applied transition —
  calls, server-push events, and state timeouts — carrying the previous state, message, reply,
  successor state, and post-transition tracks. A nil sink costs nothing.
- `Accord.TLA.TraceSpec.generate/2` produces a replay module that `EXTENDS` the generated spec:
  the recorded states become a `Trace` sequence, and each replay step requires `Next` (some
  protocol action) to produce exactly the recorded successor while an index variable advances.
  A step no action can reproduce is a TLC deadlock at that index — the divergence point. A
  completed trace self-stutters, so full replay terminates cleanly.
- Domains are synthesized from the values actually observed in the trace (exact per-track value
  sets, observed integers/atoms/strings for message parameters), which sidesteps the
  finite-domain problem entirely: a fence token of 12841 needs no `0..3` truncation.
- `Accord.Test.TraceCheck.assert_replays/3` and `assert_diverges/3` are the test harness,
  `:tlc`-gated like the other TLC assertions.

Pinned against real TLC: a genuine JobQueue session (including a pushed expiry event) replays
as a behavior of the spec; a corrupted successor state is rejected at exactly its step; a
fabricated stale-token checkout is refused by the `where:` fencing constraint in replay.

## Consequences

- Translation bugs in accord's TLA+ compiler are now detectable: a mistranslated guard or a
  dropped update produces a spec that rejects traces the real monitor emits.
- Traces are limited to values with TLA+ literal renderings (integers, atoms, strings,
  booleans, nil); anything else is an explicit `{:unsupported_term, value}` error, not a wrong
  spec. Multi-session replay is out of scope — a trace is one monitor's session.
- Correspondence counters are not pinned by the replay; they evolve through `Next` unconstrained
  by the recording, which is sound (any consistent evolution suffices).
- Wiring replay into every ProtocolExerciser iteration is deliberately not done: each TLC run
  pays JVM startup (~0.5s), and the exerciser runs hundreds of sequences. The intended pattern
  is one representative captured session per protocol in the `:tlc`-gated suite; sampling
  exerciser traces is follow-on work.
