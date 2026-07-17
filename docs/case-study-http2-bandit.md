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
