# Changelog

All notable changes to this project are documented in this file.

## 0.2.0 — 2026-09-11

The redesign release. 0.1.0 was a runtime monitor with a TLA+ emitter
bolted on; 0.2.0 is one specification checked twice, with the model
checker as a first-class design tool and the monitor as its runtime
witness. Protocols written against 0.1.0 need review: `event`, `cast`,
roles, and strict TLA+ compilation change what a declaration means.

### Protocol DSL

- `event` — server-push messages, the reverse direction end to end:
  declared in the protocol, forwarded by the monitor, modeled by TLC,
  and blamed on the server when they violate the contract.
- `cast` — one-way client messages that change state, for frame
  protocols; `where:`-guarded cast branches route conditionally, and the
  reachability pass follows state-changing cast targets.
- `role` — two-party enforcement with role-labeled blame
  (`ValidateRoles`).
- Tracks gained `shared: true` (server-side ghost state for multi-session
  checking), `domain:` for inline finite domains, `:monotonic` (no
  spurious deadlock on growing counters), and `exclusive`/`distinct`
  check kinds for cross-session mutual exclusion and uniqueness.
- `const` protocol constants substituted at compile time into every
  captured expression.
- State timeouts: monitor-initiated transitions the model also sees.
- Per-transition `timeout:` honored by the monitor.
- Inline `model do ... end` configuration, layered over protocol and
  project model files; model config files are registered as external
  resources so edits recompile the protocol.
- `ValidateTracks` rejects duplicate track names (E040).

### Runtime monitor

- `where:` reply constraints are enforced at runtime with the same
  semantics the model uses: the first branch whose type matches and whose
  constraint holds; failures surface as `:constraint_failed` with the
  track values that make the constraint evaluable.
- Correspondence counting is unified between the monitor and the model
  and enforced at runtime.
- Malformed-shape messages are rejected rather than forwarded (H5);
  track-preserving transitions are exempt from action properties (M9).
- Guard rejections carry the tracks the guard was evaluated against, and
  reports render them.

### TLA+ and model checking

- Strict spec generation by default (`tla: :strict | :warn | :off`):
  anything the model cannot faithfully express is a compile error with a
  source span (E041–E045), never a silent drop; runtime-only checks are
  labeled in the spec and in the check output.
- Multi-session checking: `sessions: N` interleaves client sessions
  against shared server state, with connection/stream composition.
- Liveness with per-action fairness via `assuming:`, scoped per property;
  terminal states self-stutter and deadlock checking is on by default.
- Boolean domains render as `BOOLEAN`; symmetry sets are emitted; atoms
  render as strings and require an enumerated domain.
- Deterministic emission (sorted state iteration), unique `MODULE` names
  with a flat artifact layout, and an abort on colliding module names.
- TLC soundness warnings are surfaced instead of swallowed; update
  `case`/`when` shapes the extractor cannot translate are rejected (C1).

### Tooling

- `mix accord.check`: content-hash pass cache (`--force` bypasses),
  per-protocol stats, `--dump` for raw TLC output, `--extra` for
  hand-written TLA+ modules extending generated specs, `-cleanup`.
- `mix accord.compat`: rolling-upgrade compatibility checking over IR
  snapshots (C001–C010) — arguments may only widen, replies only narrow,
  server pushes must stay understood, autonomous movement must not change.
- Trace validation: captured runtime traces (`trace_sink:`) replay against
  the spec (`Accord.TLA.TraceSpec`); the exerciser samples one replay per
  run (`trace_check:`).
- `Accord.Test.ExerciserFailure` renders as a single pentiment diagnostic
  with the generated session as notes ahead of the violation.
- Diagnostics syntax-highlight their source excerpts when rendered to a
  terminal (via pentiment 0.2.0 and the makeup lexers).

### Examples and case studies

- `examples/` compiles in dev and test: circuit_breaker, payment,
  job_queue (flagship), genstage_demand, each with a seeded design bug
  pinned by a real TLC run; plus `http2` (RFC 9113 against a live Bandit)
  and `phoenix_channels` (a real Phoenix endpoint, driven by both a raw
  client and Slipstream). See `docs/case-study-*.md`.

### Fixed

- `mix accord.check` no longer crashes on `__ir__/__compiled__` (`:safe`
  dropped from the term round-trip).
- TLA generation for multiple and per-session abstract track bounds.

## 0.1.0

Initial release: the compile-time protocol DSL, the gen_statem runtime
monitor with direction-derived blame, and TLA+ spec emission.
