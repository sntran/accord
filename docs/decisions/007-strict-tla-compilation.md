# ADR-007: Strict TLA+ compilation by default

## Status

Accepted (amends ADR-002 and ADR-005)

## Context

TLA+ spec generation used to be best-effort: `Accord.Protocol.compile_tla/3` rescued every
exception and downgraded it to an `IO.warn`. Two failure modes followed:

- **First compile**: no `.tla` files existed, and `mix accord.check` told the user to
  "run `mix compile` first" — a wrong instruction, since the user did compile.
- **Recompile after a breaking edit**: the *stale* spec from the previous compile remained in
  `_build/accord/`, so `mix accord.check` verified the old spec and printed a green check.
  Verified-but-wrong is the worst possible failure mode for a verification tool.

Both silently invalidate ADR-002's core claim that the TLA+ spec models exactly what the runtime
monitor enforces. A related problem: model config files were not registered as external
resources, so editing one did not trigger recompilation — another stale-spec vector.

## Decision

Spec generation failures abort compilation by default. The `tla:` option on
`use Accord.Protocol` selects the mode:

- `:strict` (default) — any spec generation failure is a compile error. A protocol that claims
  TLA+ verification either gets a faithful spec or does not compile.
- `:warn` — failures downgrade to a compiler warning, and any stale `.tla`/`.cfg` files are
  deleted so they can never be checked. The failure is recorded.
- `:off` — spec generation is skipped entirely (stale files also deleted).

Every protocol module exports `__tla_status__/0` returning `:ok`, `{:error, summary}`, or
`:off`. `mix accord.check` consults it and reports truthfully: a generation failure is a check
failure ("cannot check" must never read as "verified"), and `tla: :off` protocols are skipped
by default or failed under `--strict`.

Artifact paths, writing, and deletion are centralized in `Accord.TLA.Files` so the compiler and
the check task cannot disagree about where specs live.

## Consequences

- A green `mix accord.check` means every listed protocol was verified against a spec generated
  from its current source. No silent degradation path remains.
- Users with protocols the TLA+ compiler cannot yet translate must opt out explicitly
  (`tla: :warn` or `tla: :off`), making the unverified surface visible in the code.
- `:strict` failures currently surface as raw exceptions from the TLA+ passes; converting them
  to structured pentiment diagnostics with source spans is tracked as follow-up work
  (fidelity error codes E041–E045).
