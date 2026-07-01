# Design review: accord as a protocol design workbench (July 2026)

This document records a full design review of accord conducted in July 2026. It is the rationale
behind ADRs 007–010 and the redesign roadmap. Three independent reviews were performed: a semantic
model review, a TLA+ integration review, and a motivating-examples design. Their findings are
consolidated here.

## Summary

Accord's core architecture is sound: a single validated IR feeding two isolated pipelines (runtime
monitor, TLA+ spec) with pentiment diagnostics throughout. The safety-invariant core of the TLA+
integration delivers real verification. But the review found that roughly half of the declared
surface either does nothing or diverges from what the other pipeline enforces, and the semantic
model stops short of the protocols that motivated it — the Lock fixture is *about* multi-client
contention, yet the model cannot represent two sessions.

The redesign direction: make accord honest first (every claim either enforced or loudly marked as
not), then extend the semantics to the protocols worth designing (server-push events, multi-session
model checking), then prove it on real examples.

## Findings

### 1. Semantic model

- **F1.1 — Roles are vestigial.** `role/1` and `IR.Role` are captured into `ir.roles` and consumed
  by nothing. Blame is hard-coded by pipeline position (pre-forward failures blame the client,
  post-reply failures blame the server). The positional rule is really a consequence of message
  *direction*; making direction explicit lets blame derive from roles and makes server-push
  validation fall out naturally.
- **F1.2 — No server-push events.** Original UBF(B) had bidirectional `EVENT =>` casts. Accord has
  only client→server calls and casts, so server-initiated traffic (GenStage demand, pubsub
  broadcasts, expiry notices) bypasses the contract entirely.
- **F1.3 — Single-session model.** The generated TLA+ has one scalar `state` variable: one session.
  Cross-session safety properties (mutual exclusion, fencing) are unrepresentable, and TLC can
  never find the concurrency bugs that motivate fence tokens in the first place.
- **F1.4 — `where:` constraints are not enforced at runtime.** Branch constraints
  (`IR.Branch.constraint`) compile into TLA+ action preconditions but are never evaluated by the
  monitor — `Check.check_reply/2` selects branches by reply type only. TLC checks
  `token > tracks.fence_token`; the monitor does not. This directly violates ADR-002's claim that
  the model checks exactly what the monitor enforces.
- **F1.5 — Dead IR fields.** `Transition.from`/`to` are typed and never populated.
- **F1.6 — Per-transition timeouts** were sketched (docs/task-examples.md, Task 3) but never
  implemented; the monitor applies one global `call_timeout`.

### 2. TLA+ integration

What works: `invariant`, `local_invariant`, `bounded`, `forbidden`, and `action` checks over
tracks compile to genuine TLC invariants/action properties, with existential quantification over
message and reply domains correctly modeling adversarial peers. The counterexample-to-source
mapping (ViolationReport + pentiment) is a real strength.

What does not:

- **F2.1 — Stale-spec verification.** `Protocol.compile_tla` rescues all exceptions and downgrades
  to `IO.warn`. On first compile the spec is silently absent (and `mix accord.check` tells the
  user to "run mix compile first" — wrong instruction). On recompile after a breaking edit, the
  *previous* `.tla` remains in `_build/accord/` and `mix accord.check` verifies the stale spec and
  prints a green check. Verified-but-wrong is the worst possible failure mode for a verification
  tool.
- **F2.2 — Silently dropped updates.** The update extractor recognizes only `%{tracks | ...}`,
  `case reply do`, and block forms. `Map.put/3`, `if/else`, `cond`, and helper calls yield no
  primed assignment: the track lands in `UNCHANGED` and every invariant over it holds vacuously.
  No warning is emitted. This is the largest soundness hole found.
- **F2.3 — Missing property kinds.** `ordered` and `precedence` fall through a `nil` catch-all in
  BuildProperties and are silently absent from the spec. `reachable` emits only a comment claiming
  "verified by TLC state space exploration" — nothing asserts it. `symmetry_sets` is parsed and
  documented but no `SYMMETRY` line is ever emitted.
- **F2.4 — Correspondence diverges in both directions.** The TLA+ side counts opens/closes only on
  state-changing transitions; the monitor counts on every tag match. Worse, the monitor clamps the
  counter at zero (`max(&1 - 1, 0)`) and never reports a violation — runtime correspondence is
  write-only state. The `pending >= 0` invariant TLC checks is a property the runtime never
  enforces, over a counting discipline the runtime does not use.
- **F2.5 — The `event` variable is write-only.** Added to the state space whenever local
  invariants exist, never referenced by any generated formula. It multiplies TLC's distinct-state
  count by the number of message tags and, because it turns self-loops into variable-changing
  steps, can flip liveness verdicts when an unrelated property is added. Meanwhile the `msg`
  parameter of local-invariant functions is silently discarded by the guard compiler.
- **F2.6 — Fairness is wrong for liveness.** `FairSpec == Spec /\ WF_vars(Next)` constrains only
  "the system does not stutter forever"; it never chooses between actions. Under it, `P ~> Q`
  holds iff Q is inevitable from every reachable P-state — any client loop (ping, retry) or
  reachable terminal state makes realistic liveness properties fail, and degenerate no-op
  self-loops can make them pass accidentally. The DSL's `fairness: :weak | :strong` option is
  stored and never consumed. The divergence between runtime `timeout:` (wall-clock) and `~>`
  (untimed eventuality) is undocumented.
- **F2.7 — Deadlock checking is unconditionally disabled.** `mix accord.check` always passes
  TLC's `-deadlock` flag because terminal states have no outgoing actions and would be reported as
  deadlocks. Consequence: guard-exhaustion and stuck-state bugs are invisible in the primary
  workflow, and ViolationReport's elaborate deadlock diagnosis is dead code there. The standard
  fix (a `Terminating` self-stutter disjunct for terminal states) was never emitted.
- **F2.8 — Boolean tracks are broken.** Domain rendering emits `{"true", "false"}` (strings) while
  init and guards emit `TRUE`/`FALSE` — inconsistent spec, no fixture covers it.
- **F2.9 — Guard variable binding is name-fragile.** Identifiers not bound by declared message
  args leak into the TLA+ output verbatim; best case TLC errors, worst case they alias a track
  variable and the guard silently means something else. No compile-time validation.
- **F2.10 — Model config ergonomics.** Domains live in a separate `.exs` with no
  `@external_resource`, so editing the model file does not trigger recompilation (stale spec
  again). Defaults are invisible; a `default: 1000` track fails domain validation with a raw
  `ArgumentError`. Track-less protocols "verify" nothing while printing a green check.

### 3. Examples

- **F3.1 — No runnable examples.** The predecessor prototype had `examples/` (blackjack,
  launch_control); accord2 lost them. They died because nothing compiled them in CI.
- **F3.2 — Expressiveness gaps surfaced by writing real protocols:** protocol constants (a
  threshold literal must be duplicated across guard, update, and invariant), state timeouts
  (`open → half_open` in a circuit breaker is time-driven), correspondence closes conditioned on
  reply shape (a lease lost via an `{:expired, _}` reply cannot close its checkout), and
  track-predicate liveness (`demand > 0` leads-to delivery is inexpressible — triggers are
  `in_state/1` only).

## Decisions

Recorded as ADRs; the short form:

- **ADR-007 — Strict TLA+ compilation.** Spec generation failures are compile errors by default
  (`use Accord.Protocol, tla: :strict | :warn | :off`). Anything the model cannot faithfully
  express is a structured, span-carrying diagnostic — never a silent drop. `mix accord.check`
  reports generation status truthfully.
- **ADR-008 — Roles, events, and direction-derived blame.** Two-party protocols with an `event`
  primitive for server push; blame derives from message direction; N-party is explicitly out of
  scope (it requires projection of global protocols onto local views — a different tool).
- **ADR-009 — Multi-session model checking with ghost shared state.** `shared:` tracks and
  `sessions: N` model checking are TLC-only; the runtime monitor remains one-session-per-instance
  and treats shared tracks as per-session copies. The server is the ground truth for shared state;
  duplicating it at runtime would itself be an unverifiable distributed system. The asymmetry is
  documented, warned about (W003), and honest.
- **ADR-010 — Trace validation.** Runtime traces captured by the monitor are replayed against the
  generated spec by TLC. This is the only mechanism that can detect translation bugs in accord's
  own TLA+ compiler (TLC checks the model against itself; the property-based exerciser never
  consults the model). Apalache is deferred: the current pain is translation fidelity, not TLC
  capacity.

## Roadmap

Phases (each commit atomic and green):

- **Phase 0 — trust and drift fixes**: strict TLA+ compilation, fidelity diagnostics (E041–E045),
  `event`-variable removal, SYMMETRY emission, runtime `where:` enforcement, per-transition
  `timeout:`, duplicate-track validation (E040).
- **Phase 1 — deadlock, liveness, correspondence**: `Terminating` disjunct + deadlock checking on
  by default, per-action fairness (`assuming:`), correspondence unification (branch-resolved
  counting, unclamped runtime counter).
- **Phase 2 — roles + server-push events**: `event` macro, monitor `:downstream` + `event/2`,
  TLA+ event actions, `ValidateRoles`.
- **Phase 3 — multi-session model checking**: `shared:` tracks, `sessions: N` emission
  (byte-identical at `sessions: 1`), `exclusive` check kind, Lock fixture rework.
- **Phase 4 — expressiveness**: inline model config, protocol constants, state timeouts.
- **Phase 5 — examples**: circuit breaker, payment lifecycle, job queue with leases + fencing
  (flagship), GenStage demand — each with a seeded design bug pinned by a TLC test and a blame
  story pinned by a monitor test.
- **Phase 6 — workflow polish**: check caching, unique module names, extension modules, stats.
- **Phase 7 — trace validation.**

Deferred with reasons: Apalache backend (fidelity before capacity); N-party roles (projection);
runtime shared-track store (server is ground truth); UBF(C)-style version negotiation (no consumer
yet — a `version/1` macro without a consumer is how roles became vestigial); correspondence-over-
branches; track-predicate liveness; DBConnection and 2PC examples (2PC is the natural
post-multi-session showcase).
