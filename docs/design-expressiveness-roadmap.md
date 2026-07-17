# Expressiveness roadmap

Three features that would extend accord from session-oriented request/reply
contracts toward the broader class of OTP and wire protocols. Each is motivated
by a concrete wall hit while specifying the HTTP/2 stream state machine (see
`docs/case-study-http2-bandit.md`).

## 1. One-way state-changing messages — DONE

**Wall:** HTTP/2 frames are one-way in both directions, not request/reply. Peer
frames had to be modeled as `on` calls with dummy replies, and the
reply-refinement and server-blame machinery went inert.

**Shipped:** `cast` is now the client-side mirror of `event` — a one-way
client → server message that may change state (`goto:`), with `guard`/`update`
in a block form. A bare `cast :x` is unchanged. State-changing casts run the
full runtime pipeline (types, guard, update, properties) and are blamed on the
client; in TLA they emit the same state-changing action as an event. The HTTP/2
stream FSM re-specced with casts (no dummy replies) compiles and model-checks
identically clean.

This is the single most valuable of the three: it is what lets the **runtime
monitor** — not just the model — apply to a frame protocol, because both
directions are now first-class one-way messages the monitor can validate and
attribute.

## 2. Symbolic / large domains — Tier A DONE

**Wall (two forms).** The HTTP/2 stream-ID rule (a new ID must exceed the
highest seen) **spuriously deadlocks** at `sessions: 2` with domain `0..3`: one
stream grabs the max ID and the next starves — an artifact of a tiny domain,
impossible in HTTP/2's 2³¹ space. And the flow-control window (2³¹−1, with
overflow and negative-window rules) is unrepresentable in TLC's small finite
domains — which is exactly where the genuinely dangerous bugs live.

These are two different needs:

- **Relational properties** (monotonic, distinct, bounded) do not need the real
  values, only the relationship. The stream-ID distinctness proof holds for any
  domain large enough not to starve; the tiny domain is the only problem.
- **Value properties at scale** (the 2³¹ overflow, the §6.9.1 increment check)
  need the actual arithmetic.

**Design — two tiers, cheapest first.**

*Tier A: abstraction patterns (small, no new backend) — SHIPPED.* A track
modifier for quantities whose properties are relational: `track :last_id,
:non_neg_integer, abstract: :monotonic, domain: 0..3`. The emitter extends the
declared domain by one head-room value and adds a `StateConstraint` conjunct
(`last_id =< 3`) that stops exploration at the declared bound instead of at
domain exhaustion — so a session that cannot advance because it has hit the
exploration bound stutters (bounded-checking boundary) rather than registering a
false deadlock. This directly fixes the stream-ID spurious deadlock and covers
monotonic/distinct/bounded properties (`test/support/protocols/monotonic_id.ex`
proves a `distinct` id across two sessions with deadlock checking on). It does
*not* model 2³¹ overflow — that is Tier B.

*Tier B: an Apalache backend (large, deferred).* Apalache checks TLA+
symbolically via SMT, so a 32-bit window with real arithmetic is in reach. It
requires a second emission target with type annotations (`@type` comments) and
loses some of TLC's liveness support, and the original review deferred it
deliberately (*fidelity before capacity*). The intermediate structs already keep
types symbolic to hold the door open. Recommendation: build Tier A first — it
retires the common case at low risk — and reserve Apalache for protocols whose
correctness genuinely turns on large-value arithmetic.

## 3. Protocol composition / layered state — largely expressible today

**Wall (as first stated).** The HTTP/2 state machine is split across two modules:
the per-stream FSM (`stream.ex`) and the connection-level rules (`connection.ex`,
`stream_collection.ex`) — stream-ID monotonicity, max-concurrent-streams,
connection GOAWAY. The concern was that a single accord protocol could not hold
both, so the connection-level rules that gate the stream FSM (no new stream after
GOAWAY; the shared window) could not be expressed together with it.

**Finding.** After features 1 and 2 landed, the composition the case study needs
is already expressible — no dedicated two-level construct required. The three
existing primitives compose:

- **`shared:` tracks** carry connection-level state (a `conn_state`, a
  `last_stream_id`) that every session reads.
- **A state-changing `cast`** (feature 1) is the connection event that flips that
  shared state — `cast :goaway` sets `conn_state: :going_away` from any state.
- **`abstract: :monotonic`** (feature 2) keeps the shared stream-ID counter finite
  under the monotonic open-guard.
- Per-session **guards read the shared track**, so the stream-open branch is gated
  on `conn_state == :active`.

`test/support/protocols/conn_gate.ex` is the whole HTTP/2 connection/stream gate
in one protocol: `ConnGate` proves (TLC, `sessions: 2`) that no stream opens once
GOAWAY has been cast; `ConnGateUnguarded` drops the `conn_state == :active` guard
and TLC finds the stream that opens after GOAWAY. The "connection FSM" is modeled
as shared state flipped by a cast rather than a second nested state machine — for
the gating rules that matter (admit/reject a stream against connection state),
that is sufficient and checked for real.

One emitter bug blocked this until fixed: a boolean track assigned from a
comparison (`open_seen_goaway' = conn_state = "going_away"`) tripped a TLA
precedence conflict. `BuildActions.parenthesize_value/1` now wraps update values
whose top level is a comparison; see the feature-3 commit.

**Remaining gap (ergonomic, not expressive).** What is *not* here is a genuinely
separate connection protocol module with its own multi-state FSM that a stream
protocol is declared inside. Today the connection is one shared track flipped by a
cast; a two-state (or N-state) connection lifecycle with its own transitions,
distinct from the session FSM, would need a real nesting construct
(`sessions_of`). That buys ergonomics and a cleaner blame story (connection vs
stream), not new checking power for the GOAWAY-gating class — that class is
covered now. Defer the construct until an example needs a connection FSM richer
than a single flag.

## Order

1. **Done:** one-way messages (`cast` with state change).
2. **Done:** Tier-A abstract/monotonic domains — retires the stream-ID
   spurious-deadlock class and most relational properties.
3. **Done for the gating class:** protocol composition via `shared:` + `cast` +
   `abstract` (`conn_gate.ex`). A dedicated `sessions_of` nesting construct is
   deferred until an example needs a multi-state connection lifecycle.
4. **Deferred:** Apalache — only for correctness that turns on large-value
   arithmetic (flow-control overflow).

## Application: accord as a conformance firewall

A monitor that sits between a client and a server can do more than *observe*. In
the HTTP/2 example (`examples/http2/tap_proxy.ex`) it forwards bytes verbatim and
taps the frame stream to assign blame. The same position supports a second mode:
**gate** the traffic — drop frames the spec forbids before they reach the server.
This is a practical way to mitigate a buggy server while an upstream fix is
pending: enforce the conformance the server itself does not.

Concretely, for the §8.1 trailers bug, a gate would drop the client's malformed
trailing HEADERS frame before Bandit sees it, so Bandit only ever receives the
well-formed frames and cannot fold post-trailer DATA into the body. The operator
gets RFC-conformant behavior from a non-conformant server, at the proxy, today.

**The design has a subtlety worth stating, because building the server-catch
(Round 3) surfaced it.** The two modes want *opposite* specs:

- **Observe / server-catch.** A malformed client frame is the expected trigger;
  the spec *accepts* it and routes to a server-obligation state (`:reset_expected`,
  `:goaway_expected`) so the server's response is judged. The frame is not a
  violation here — the server's failure to reset is.
- **Gate / firewall.** The malformed client frame is exactly what to *reject*. The
  gate needs a client-conformance stance where that frame has no legal transition,
  so the monitor rejects it — and the gate then drops its bytes rather than
  forwarding them, leaving the stream in its pre-frame state so valid traffic
  continues.

So a firewall is not the observe-mode monitor run backwards; it wants a spec that
declares the client's obligations (reject bad frames) rather than the server's
(demand a reset). Both derive from the same protocol, but they enumerate different
transitions. A production gate would: buffer client→server bytes, extract complete
frames, run each through a client-conformance monitor, forward the accepted
frames' bytes and drop the rejected ones (optionally answering the client with a
RST_STREAM/GOAWAY of the correct error code — the very code Round 2 showed Bandit
gets wrong). The blame direction tells the gate which side to act on: reject and
drop **client**-blamed frames; surface **server**-blamed responses to the operator
(you cannot un-send the server's bytes, but you can alarm on them).

**Status.** The observe-mode proxy is built and tested; the gate mode is a
documented design, not yet implemented. The frame-level buffering and the second
(client-conformance) spec are the work. It is a genuinely useful direction — a
spec-derived conformance firewall is something a hand-rolled filter is not — and a
natural next step for the example.
