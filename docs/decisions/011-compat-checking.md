# ADR-011: Protocol compatibility checking

## Status

Accepted

## Context

UBF(C) envisioned contract negotiation between peers. The practical BEAM version of that problem
is the rolling upgrade: servers and clients deploy at different times, so for a window the old
contract's clients talk to the new contract's server. Nothing checked whether that window is
safe — a removed message, a narrowed argument type, or a new reply shape breaks deployed
clients silently.

The original redesign deferred this deliberately: "do not add a `version/1` macro until its
consumer exists" — a version declaration without a checker is exactly how `role/1` became
vestigial the first time.

## Decision

**Ship the consumer; skip the version macro entirely.**

`Accord.Compat.check(old, new)` is a static state-by-state simulation over two IRs answering:
*can clients speaking `old` talk to a server monitored by `new`?* Deploy servers first when it
holds; the same function answers the client-first dual as `check(new, old)`.

The rules (C001–C009 errors, C010 advisory):

- states old clients track must exist and stay non-terminal;
- messages old clients send must stay accepted, same kind, with argument types only *widening*
  (contravariance, via the new `Accord.IR.Type.subtype?/2` relation);
- replies the new contract permits must all be understood by old clients (types only
  *narrowing* — covariance) and must lead to the state the old client will assume;
- server pushes must be events old clients handle, covariant payloads, matching targets;
- state timeouts must not change the session's autonomous movement;
- added or changed guards/`where:` constraints are advisories — refusal-freedom is not
  statically decidable, so the check reports the change and defers to review.

**Versioning is a snapshot, not a macro.** `mix accord.compat --snapshot Module path.ir`
serializes the IR into the repo; `mix accord.compat Module --against path.ir` gates changes in
CI. The snapshot *is* the released contract — it cannot drift from what shipped, and no
declaration in the DSL can go stale against it.

## Consequences

- Rolling-upgrade safety becomes a CI property: snapshot on release, check on every PR.
- The check is conservative and structural: renamed states or behaviorally-equivalent guard
  rewrites report as incompatibilities/advisories. A clean result is trustworthy; a finding may
  need human judgment (especially C010 guard advisories).
- `Type.subtype?/2` is deliberately `false`-leaning — unknown type combinations never silently
  pass — and its soundness law (values of the subtype pass the supertype's runtime check) is
  property-tested.
- Behavioral refinement checking (old contract simulates new via TLC refinement mapping)
  remains future work; the static check covers the message-shape compatibility that breaks
  deployed clients in practice.
- Snapshots share the `binary_to_term` trust boundary of compiled protocol IRs: repository
  artifacts, not untrusted input.
