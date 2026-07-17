# Case study: HTTP/2 stream state machine (Bandit)

A test of accord against a real, high-profile protocol: the HTTP/2 stream state
machine as implemented by [Bandit](https://github.com/mtrudel/bandit) 1.12.0. It
produced a runtime-confirmed RFC-compliance divergence in Bandit, and a precise
map of where accord's expressiveness ends.

## What I did

1. Read Bandit's HTTP/2 stream machinery: `stream.ex` (per-stream state machine),
   `connection.ex` (frame routing), `stream_collection.ex` (stream-ID rules),
   `flow_control.ex` (window accounting).
2. Wrote two accord specs — the single-stream state machine, and the
   connection-level stream-ID monotonicity rule — and model-checked both with
   real TLC.
3. Diffed the RFC-faithful spec against Bandit's code and found a divergence.
4. Confirmed it at runtime with a probe in Bandit's own test suite.

## What I found

**Bandit silently drops frames sent on a lower-numbered stream ID, where RFC 9113
§5.1.1 requires a connection error of type PROTOCOL_ERROR.**

`Bandit.HTTP2.StreamCollection.get_pid/2` classifies a stream ID as `:new` only
when `id > last_stream_id`; a lower ID not currently active returns `:closed`, and
`Bandit.HTTP2.Stream.deliver_headers(:closed, …)` is a no-op. So a HEADERS frame
that tries to open a stream with an ID below one already used is swallowed — no
GOAWAY, connection stays open.

RFC 9113 §5.1.1: *"The identifier of a newly established stream MUST be numerically
greater than all streams that the initiating endpoint has opened or reserved … An
endpoint that receives an unexpected stream identifier MUST respond with a
connection error of type PROTOCOL_ERROR."*

Assessment: it is a real MUST violation, but lenient — no crash, no leak; a
misbehaving peer is ignored rather than allowed to tear down the connection.
Defensible as robustness. The downside is a worse failure mode for a buggy client:
it hangs waiting for a response that never comes, instead of receiving a clean
PROTOCOL_ERROR. Bandit has no code referencing §5.1.1 and no test for the lower-ID
case (its tests cover only the higher/idle case, which correctly errors). Worth
raising with the maintainer as "is this intended?" — not a security issue.

## The specs

**Single-stream FSM** (`stream.ex` + RFC §5.1). Five states, ~20 transitions;
peer frames modeled as client messages, Bandit's frames as server-push `event`s;
each frame split into a plain and an `_es` (END_STREAM) tag because accord
dispatches by tag. Model-checked clean by TLC (5 distinct states, no deadlock).

```elixir
state :idle do
  on :headers, reply: :ok, goto: :open
  on :headers_es, reply: :ok, goto: :remote_closed
  # DATA/WINDOW_UPDATE/RST in :idle are undeclared -> invalid_message (the
  # connection error Bandit raises).
end

state :open do
  on :headers_es, reply: :ok, goto: :remote_closed
  on :data, reply: :ok, goto: :open
  on :data_es, reply: :ok, goto: :remote_closed
  on :window_update, reply: :ok, goto: :open
  on :rst_stream, reply: :ok, goto: :closed
  event :s_data, goto: :open
  event :s_data_es, goto: :local_closed
  # ... s_headers / s_headers_es likewise
end

state :remote_closed do   # peer sent END_STREAM
  on :window_update, reply: :ok, goto: :remote_closed
  on :rst_stream, reply: :ok, goto: :closed
  event :s_data_es, goto: :closed
  # DATA/HEADERS from the peer here are undeclared -> STREAM_CLOSED
end

state :local_closed do    # Bandit sent END_STREAM
  on :data_es, reply: :ok, goto: :closed
  on :window_update, reply: :ok, goto: :local_closed
  on :rst_stream, reply: :ok, goto: :closed
  # ...
end

state :closed, terminal: true
```

**Connection-level stream-ID rule** (`stream_collection.ex`). A new stream ID must
strictly exceed the highest seen — a fence token. Modeled as `sessions: 2` streams
sharing the connection's `last_id`. TLC proves `distinct :my_id` for the guarded
version; the unguarded version fails.

```elixir
track :last_id, :non_neg_integer, default: 0, shared: true, domain: 0..3
track :my_id, :non_neg_integer, default: 0, domain: 0..3

model do
  sessions 2
end

state :idle do
  on :open_stream do
    branch({:opened, id :: pos_integer()}, goto: :active,
      where: fn {:opened, id}, tracks -> id > tracks.last_id end)
    update fn _msg, {:opened, id}, tracks -> %{tracks | last_id: id, my_id: id} end
  end
end
# ...
property :ids_distinct do
  distinct :my_id, empty: 0
end
```

## How to test the bug

Add this to Bandit's `test/bandit/http2/protocol_test.exs` (reuses `SimpleH2Client`):

```elixir
test "HEADERS on a lower stream id after a higher one", context do
  socket = SimpleH2Client.setup_connection(context)

  # Open and complete stream 3 (last_stream_id -> 3).
  {:ok, ctx} =
    SimpleH2Client.send_simple_headers(socket, 3, :get, "/no_body_response", context.port)
  assert SimpleH2Client.successful_response?(socket, 3, false)
  assert {:ok, 3, true, ""} = SimpleH2Client.recv_body(socket)

  # HEADERS on stream 1 (lower). RFC 9113 §5.1.1: MUST be a connection error.
  SimpleH2Client.send_simple_headers(socket, 1, :get, "/no_body_response", context.port, ctx)

  # RFC-compliant would be a GOAWAY; today the connection stays alive.
  refute SimpleH2Client.connection_alive?(socket)
end
```

Observed today: `connection_alive?/1` returns `true` (silently dropped). The test as
written fails, documenting the divergence; a compliant server would send a GOAWAY
and close, making `recv_goaway_and_close/1` the expected assertion.

## How to fix it

The divergence is in `Bandit.HTTP2.Connection.with_stream/3` (and the classification
in `Bandit.HTTP2.StreamCollection.get_pid/2`). `get_pid/2` conflates two RFC states:

- **implicitly closed** — a lower ID never opened (`id < last_stream_id`, not in the
  map): frames here are unexpected;
- **explicitly closed** — a stream that was opened and completed: leniency is
  appropriate here for races.

Both currently return `:closed` and are dropped. The fix is to distinguish them.
A minimal version: in `with_stream/3`, when `get_pid/2` returns `:closed` for a
HEADERS frame whose stream ID was never active, raise a connection error of type
`PROTOCOL_ERROR` rather than delivering to the `:closed` no-op. (Recently-closed
streams should keep their current lenient handling of WINDOW_UPDATE/RST_STREAM.)

## What this says about accord

accord did **not** find this automatically. Its runtime monitor doesn't fit HTTP/2
(frames are one-way in both directions, not call/reply), and TLC checked the spec
against itself, never Bandit's code. What surfaced the bug was the discipline of
writing the spec: enumerating the exact legal-frame-per-state table made Bandit's
`:closed`-drop visible on a read. accord's value here is as a **forcing function for
precise specification**, not an automatic bug-finder.

Four expressiveness walls, in the order they bit:

1. **`on`/`event` asymmetry.** HTTP/2 frames aren't request/reply, so peer frames
   needed dummy replies, and accord's reply-refinement and server-blame machinery
   went inert. (Since addressed: `cast` now carries one-way state-changing client
   messages — see `docs/design-expressiveness-roadmap.md` §1.)
2. **END_STREAM flag → tag explosion.** Dispatch is by tag, so a flag became four
   messages.
3. **The FSM is split across two modules and can't be one accord protocol.** Stream
   states live in `stream.ex`; the ID/concurrency/flow-control rules live at the
   connection level. Two separate specs were required.
4. **Finite-domain ceiling.** The stream-ID spec spuriously deadlocks at
   `sessions: 2` with domain `0..3` (a stream grabs the max ID; the next starves).
   HTTP/2's 2³¹ ID space is unrepresentable; flow-control's window arithmetic —
   where the genuinely dangerous bugs live — is out of reach entirely.

---

# Round 2: flow control and SETTINGS error codes

A second pass, after `cast`, `abstract:`/bounded domains, and the connection/stream
composition pattern landed (walls 1 and 4 above are now partly retired). This pass
moved from the stream state machine into frame validation — WINDOW_UPDATE, DATA,
and SETTINGS — and produced two more runtime-confirmed divergences, plus the first
flow-control property accord model-checks for real.

## Two more divergences: the wrong error code for a valid-but-illegal value

Both are `MUST` violations where Bandit returns a plausible-but-wrong error code,
and both are pinned by Bandit's own deserialization tests (so they are intended
behavior, not a slip). In each case a *sibling* check a few lines away uses the
correct code, which is what makes them stand out.

**A. Zero-increment WINDOW_UPDATE → `FLOW_CONTROL_ERROR`, should be
`PROTOCOL_ERROR` (RFC 9113 §6.9).**

`Bandit.HTTP2.Frame.WindowUpdate.deserialize/3` rejects a zero size increment with
`Bandit.HTTP2.Errors.flow_control_error()` (`0x3`). RFC 9113 §6.9, verbatim:

> A receiver MUST treat the receipt of a WINDOW_UPDATE frame with a flow-control
> window increment of 0 as a stream error (Section 5.4.2) of type PROTOCOL_ERROR;
> errors on the connection flow-control window MUST be treated as a connection
> error (Section 5.4.1).

So the required code is `PROTOCOL_ERROR` (`0x1`), not `FLOW_CONTROL_ERROR`. The
adjacent overflow check (`update_send_window`, §6.9.1) correctly uses
`FLOW_CONTROL_ERROR` — §6.9.1 overflow and §6.9 zero-increment are two different
rules with two different codes, and Bandit applies the overflow code to both.

There is a second, subtler half: §6.9 says the *stream*-scoped case is a **stream
error** (RST_STREAM on that stream), and only the connection-flow-control-window
case is a connection error. Bandit routes all frame-deserialization failures
through `handle_frame` as connection errors (`frame.ex` notes it considers this
within its rights for size errors), so a zero-increment WINDOW_UPDATE on one
stream tears down the **whole connection** — every concurrent request on it — where
the RFC calls for resetting just that one stream. That escalation is the more
material half; the wrong code is the clear-cut half.

Pinned by `test/bandit/http2/frame_deserialization_test.exs` ("rejects frames when
there is a 0 size increment" and "… on a stream"), both asserting
`Errors.flow_control_error()`.

**B. Out-of-range MAX_FRAME_SIZE → `FRAME_SIZE_ERROR`, should be `PROTOCOL_ERROR`
(RFC 9113 §6.5.2).**

`Bandit.HTTP2.Frame.Settings.deserialize/3` rejects a `SETTINGS_MAX_FRAME_SIZE`
value below 2¹⁴ or above 2²⁴−1 with `frame_size_error()` (`0x6`). RFC 9113 §6.5.2,
verbatim:

> Values outside this range MUST be treated as a connection error (Section 5.4.1)
> of type PROTOCOL_ERROR.

So the required code is `PROTOCOL_ERROR` (`0x1`). The name `FRAME_SIZE_ERROR` is
tempting because the setting is *about* frame size, but the frame here is
well-formed — it is the advertised *value* that is illegal, which the RFC classes
as a protocol error. The two sibling checks in the same function get it right:
`ENABLE_PUSH` (not 0/1) → `PROTOCOL_ERROR`, `INITIAL_WINDOW_SIZE` (> 2³¹−1) →
`FLOW_CONTROL_ERROR`. Only `MAX_FRAME_SIZE` is miscoded.

Pinned by `test/bandit/http2/frame_deserialization_test.exs` ("rejects non-ack
frames with invalid large/small max_frame_size value"), asserting
`Errors.frame_size_error()`.

**Impact (both).** Low. A conformant peer never sends these, and a misbehaving one
still receives an error and a teardown — only the code differs, and few clients
branch on it. A conformance suite (h2spec) would flag both. Finding A's stream →
connection escalation is the one place a real client is measurably worse off. Worth
raising with the maintainer as "intended?", not a security issue.

**Fix.** Change the three returns to `protocol_error()` (WINDOW_UPDATE zero
increment; both MAX_FRAME_SIZE bounds) and update the pinning tests. For finding
A's escalation, route a zero-increment WINDOW_UPDATE carrying a non-zero stream ID
to a stream reset rather than a connection error — a larger change, since it means
distinguishing stream-scoped from connection-scoped deserialization failures.

## How accord fits: blame is coarser than the RFC's error taxonomy

The pattern in both findings is the same, and it is exactly what an accord spec
makes visible. A zero-increment WINDOW_UPDATE and an out-of-range MAX_FRAME_SIZE
are both **client** (peer) protocol violations — accord's blame trichotomy
classifies them identically as "the peer sent a message the contract forbids."
What accord's blame does *not* carry is *which* of RFC 9113 §7's fourteen error
codes the server must emit in response. That taxonomy lives one level below blame.

So the accord discipline puts the two questions side by side — "who is at fault?"
(the guard/`where:` that fails → the peer) and "what does the server answer?" (the
error code) — and writing the second column explicitly is what exposes that Bandit
answers with the field's *namesake* code (`FLOW_CONTROL_ERROR` for a window field,
`FRAME_SIZE_ERROR` for a frame-size field) where the RFC mandates `PROTOCOL_ERROR`.
`when value > @max`-style guards scattered across a deserializer hide that column;
a contract that names an outcome per rejection surfaces it. This is the same
"forcing function, not auto-finder" lesson as Round 1, sharpened: the gap accord
exposes is between *blame* (coarse, who) and *error code* (fine, what).

## The part accord checks automatically: the §6.9.1 overflow guard

Unlike the error codes — frame-validation facts outside the state machine — the
send-window overflow rule *is* a state-machine property, and with the new
expressiveness accord model-checks it. The spec (`/tmp/h2_flow.exs`, correct and
seeded-buggy variants) models the server's per-stream send window as a bounded
track, the peer's WINDOW_UPDATE as a one-way `cast`, and the server's DATA as a
one-way server-push `event`, with the ceiling as a `const`:

```elixir
const :max, 3
track :send_window, :non_neg_integer, default: 1, domain: 0..6

state :open do
  # Peer grants quota. §6.9.1: the increment must not push us past the ceiling.
  cast {:window_update, inc :: pos_integer()} do
    guard fn {:window_update, inc}, tracks -> tracks.send_window + inc <= const(:max) end
    update fn {:window_update, inc}, tracks -> %{tracks | send_window: tracks.send_window + inc} end
  end

  # Server pushes DATA, never more than the window allows.
  event {:send_data, n :: pos_integer()} do
    goto :open
    guard fn {:send_data, n}, tracks -> n <= tracks.send_window end
    update fn {:send_data, n}, tracks -> %{tracks | send_window: tracks.send_window - n} end
  end
end

property :window_never_overflows do
  invariant fn tracks -> tracks.send_window <= const(:max) end
end
```

This is the same `guard` accord's runtime monitor would enforce and TLC exhausts.
TLC proves `window_never_overflows` for the guarded version. Dropping the guard —
the seeded bug, mirroring a deserializer that forgets the §6.9.1
`current + increment > max` check — yields a two-state counterexample:
`send_window = 1` → (one WINDOW_UPDATE, `inc = 3`) → `send_window = 4`, overshooting
the ceiling of 3. This is the first HTTP/2 flow-control fact accord checks for real
rather than narrates: Round 1's wall 4 ("window arithmetic is out of reach") is
retired for the *relational* overflow guard by bounded domains, though the literal
2³¹ ceiling still needs Tier-B symbolic checking (Apalache).

Three expressiveness pieces made this spec possible that Round 1 lacked: `cast` for
the one-way peer WINDOW_UPDATE, `event` for the one-way server DATA (over-delivery
would be server blame at runtime), and `const` + a bounded head-room domain for the
ceiling. The remaining wall is unchanged: the zero-increment rule itself is *not*
model-checkable here, because accord types the increment `pos_integer`, so `0` is
excluded from the state space by construction — confirming from the other direction
that the zero-increment error code is a frame-parsing concern below the protocol's
typed domain, not a state-machine one.
