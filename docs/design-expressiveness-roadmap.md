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

## 2. Symbolic / large domains

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

*Tier A: abstraction patterns (small, no new backend).* Add a track modifier for
quantities whose properties are relational, e.g. `track :last_id,
:non_neg_integer, abstract: :monotonic`. The emitter models it as a counter
bounded only by a `StateConstraint` for exploration (bounded checking), and
suppresses the deadlock that comes from *exhausting* the abstract domain — a
stream that cannot advance because the abstract counter is at its exploration
bound is a modeling boundary, not a real stuck state, so it stutters rather than
deadlocks. This directly fixes the stream-ID spurious deadlock and covers
monotonic/distinct/bounded properties. It does *not* model 2³¹ overflow.

*Tier B: an Apalache backend (large, deferred).* Apalache checks TLA+
symbolically via SMT, so a 32-bit window with real arithmetic is in reach. It
requires a second emission target with type annotations (`@type` comments) and
loses some of TLC's liveness support, and the original review deferred it
deliberately (*fidelity before capacity*). The intermediate structs already keep
types symbolic to hold the door open. Recommendation: build Tier A first — it
retires the common case at low risk — and reserve Apalache for protocols whose
correctness genuinely turns on large-value arithmetic.

## 3. Protocol composition / layered state

**Wall.** The HTTP/2 state machine is split across two modules: the per-stream
FSM (`stream.ex`) and the connection-level rules (`connection.ex`,
`stream_collection.ex`) — stream-ID monotonicity, max-concurrent-streams,
connection GOAWAY. A single accord protocol cannot hold both, so the case study
needed two separate specs, and the connection-level rules that gate the stream
FSM (no new stream after GOAWAY; the shared flow-control window) could not be
expressed together with it.

`sessions: N` + `shared:` tracks is a *partial* composition: N sessions of **one**
protocol sharing scalar state. What is missing is a **second protocol level**
with its own state machine that constrains the sessions.

**Design.** A connection-level protocol that owns connection state and rules, with
the stream protocol running as sessions inside it:

```elixir
defmodule Http2.Connection do
  use Accord.Protocol

  # Connection-level state machine and shared state.
  initial :active
  track :last_stream_id, :non_neg_integer, default: 0, domain: 0..3

  state :active do
    on :goaway, reply: :ok, goto: :going_away
  end

  state :going_away, terminal: true

  # The stream protocol runs as sessions within this connection.
  sessions_of Http2.Stream do
    # A new stream may open only while :active, with a fresh id.
    guard_open fn conn, stream_id -> conn.state == :active and stream_id > conn.last_stream_id end
    on_open fn conn, stream_id -> %{conn | last_stream_id: stream_id} end
  end
end
```

The connection protocol's state (`going_away`) and shared tracks
(`last_stream_id`) gate the stream sessions; the stream sessions read connection
state in their guards. In TLA this is a product: connection variables plus
per-session stream variables, with stream actions carrying the connection
preconditions. At runtime it is a supervising monitor that owns the connection
state and admits/rejects stream messages against it.

This is the largest of the three — it introduces genuine two-level state and a
composed TLA product — and it is what would let a real layered protocol
(HTTP/2, but also multiplexed session protocols generally) be one checkable
model rather than several. Recommend it after Tier-A domains, since layered
state and shared counters interact (the connection's `last_stream_id` is exactly
the abstract-monotonic case above).

## Order

1. **Done:** one-way messages (`cast` with state change).
2. **Next, cheap:** Tier-A abstract/monotonic domains — retires the stream-ID
   spurious-deadlock class and most relational properties.
3. **Then:** protocol composition — the connection/stream two-level model.
4. **Deferred:** Apalache — only for correctness that turns on large-value
   arithmetic (flow-control overflow).
