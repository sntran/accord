# ADR-008: Roles, server-push events, and direction-derived blame

## Status

Accepted (extends ADR-003)

## Context

Two gaps separated accord from the UBF vision it resurrects:

1. **Roles were vestigial.** The `role/1` macro existed and was captured into the IR, but
   nothing consumed it. Blame was hard-coded by pipeline position: checks before the upstream
   call blamed the client, checks after it blamed the server.
2. **No server-push events.** Original UBF(B) had bidirectional `EVENT` casts. Accord validated
   only client → server traffic, so server-initiated messages — demand-driven data, expiry
   notices, pubsub broadcasts — bypassed the contract entirely. Real BEAM protocols (GenStage,
   DBConnection, Phoenix channels) are full of them.

The key insight: pipeline-position blame is a *consequence* of message direction. The client is
blamed for a bad call because the client sent it. Making direction explicit lets blame derive
from the sender, and server-push validation falls out of the same rule.

## Decision

**Two-party protocols with direction-derived blame.** The first declared role initiates calls
and casts (default `:client`); the second replies and pushes events (default `:server`).
`Accord.Pass.ValidateRoles` rejects more than two roles (E050) and duplicates (E051). Declared
role names label blame in violations (`context.role`) and log lines; the canonical ternary blame
API (`:client | :server | :property`, ADR-003) is unchanged.

**The `event` primitive.** `event message_spec` declares a server push valid in a state, with
`guard` (fn message, tracks), arity-2 `update`, and `goto:` — events may change state, which
anystate calls cannot. Events have no reply surface (E004 rejects replies/branches/timeouts).

**Pushes go through the monitor.** Consistent with ADR-001's explicit-proxy stance, the server
sends events via `Accord.Monitor.event/2`; the monitor validates them against the current state
and forwards them to the `:downstream` pid with `send/2` (nil = validate-only). Everything a
pushed event violates blames the server: undeclared push → `:invalid_event`, bad payload →
`:argument_type`, guard failure → `:guard_failed`, push after terminal → `:session_ended`.

**Events are actions in the model.** Each event becomes one more TLA+ action interleaved with
client calls, so TLC explores request/push races a single-direction model cannot represent.

## Consequences

- Protocols like the GenStage demand contract become checkable: the event guard *is* the
  documented "never exceed demand" rule, enforced at runtime with server blame and verified
  exhaustively by TLC.
- The server must cooperate by pushing through the monitor. A server that sends directly to the
  client bypasses validation — the same trust assumption ADR-001 already makes for calls.
- N-party protocols are explicitly out of scope: they require projecting a global protocol onto
  per-participant local views (multiparty session types), and the monitor is architecturally a
  two-endpoint proxy. The IR keeps roles as a list so a future projection tool is not precluded.
- A call and an event cannot share a message tag in one state (E020 ambiguous dispatch) — the
  transition table lookup stays unambiguous.
