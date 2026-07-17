# Phoenix Channels

accord as a **conformance monitor for the Phoenix Channels protocol** — the
realtime transport under Phoenix Channels *and* LiveView, which has no conformance
tooling of its own (phoenix.js is a client, not an oracle; there is no h2spec /
Autobahn analogue for the channel semantics).

Unlike the HTTP/2 example — where h2spec already checks the same server — this
protocol is genuinely unguarded, and the monitor catches a class of bug Phoenix
**structurally cannot**: obligations the framework leaves to your channel code.

## What it is

A conformant accord model of the per-topic channel lifecycle, plugged into a real
Phoenix endpoint through a one-line serializer, checking every channel message in
both directions and assigning blame.

```
raw WS client ──frames──▶ Phoenix endpoint ──▶ Serializer (wraps v2 JSON)
                                                    │ taps decode!/encode!
                                                    ▼
                                                  Tap ──▶ per-topic Channel monitor
```

- **`channel.ex`** — the accord contract: per-`(topic)` FSM
  `not_joined → joining → joined → leaving → closed`, client frames as `cast`s,
  server frames as server-push `event`s, and a `pending` counter enforcing the
  reply obligation. Model-checked by TLC (`assert_passes`).
- **`serializer.ex`** — a `Phoenix.Socket.Serializer` that wraps the real v2 JSON
  serializer and taps every message. **This is the whole integration surface** —
  one line in any Phoenix app turns the monitor on:

  ```elixir
  socket "/socket", MySocket,
    websocket: [serializer: [{Accord.Examples.PhoenixChannels.Serializer, "~> 2.0.0"}]]
  ```

- **`tap.ex`** — holds one channel monitor per topic, routes tapped messages, and
  applies the runtime-only join_ref discipline.
- **`app.ex`** — a demo endpoint, a correct `RoomChannel`, and a `BuggyChannel`
  that replies twice to one request.
- **`ws_client.ex`** — a minimal raw WebSocket client that can send the adversarial
  sequences a real client library refuses to.

## What it catches (`test/examples/phoenix_channels_test.exs`)

Against a **real running Phoenix endpoint**:

| Scenario | accord verdict |
|----------|----------------|
| normal join / push+reply / leave | **no violations** (faithful to real traffic) |
| a channel that replies twice to one request | **server** blame (`guard_failed`: nothing pending) |
| a push before joining the topic | **client** blame (`invalid_message`) |
| a stale `join_ref` (Phoenix drops it silently) | **client** blame — the silent drop made visible |
| a server-initiated push mid-session | no violation |

Two of these are the point:

- **The reply obligation.** Phoenix does not track "one reply per request" — a
  `handle_in` that replies twice, or replies to a `ref` no client sent, violates
  the protocol and the framework does not stop it. That obligation lives in *your*
  channel code, and this is where a real app has real bugs. `BuggyChannel`'s
  double `reply/2` is caught as server blame; a normal channel raises nothing.
- **Making silent failures visible.** A stale `join_ref` (from a client that
  rejoined but kept an old ref) is **silently dropped** by Phoenix — no reply, no
  log, the message just vanishes. That is the classic "why did my events stop
  arriving?" bug. The monitor surfaces it with blame.

## Running it

```bash
# Model-check the channel lifecycle (needs tla2tools.jar):
mix test test/examples/phoenix_channels_test.exs --only tlc

# Live, against a real Phoenix endpoint (Phoenix is a dev/test dependency):
mix test test/examples/phoenix_channels_test.exs
```

## Honest scope

- **Monitors are keyed by topic.** A channel's push replies are encoded in the
  channel process while its join reply is encoded in the connection process, so
  `self()` is not a stable per-connection key. Per-topic keying means one
  connection at a time per topic — sufficient for the demo; concurrent connections
  on one topic would share a monitor.
- **join_ref discipline is runtime-only.** join_refs are arbitrary strings, not
  model-checkable, so the tap enforces it (recording the join_ref at join,
  rewriting a stale client message to `:stale_message`) rather than TLC.
- **Duplicate join is not modeled.** Re-joining an already-joined topic makes
  Phoenix evict the old channel and rejoin (emitting a `phx_close` for the old
  one). That client anti-pattern (the JS client prevents it) is flagged as a
  duplicate-join client violation, but the evict-and-rejoin sequence then produces
  a spurious follow-on violation. Modeling it cleanly would need a rejoin path; it
  is left as a known boundary.
- **Broadcasts via fastlane** are encoded once in the broadcasting process, not
  per connection, so a broadcast is observed but cannot be attributed to a
  specific connection. The demo uses `push/3` (per-connection `encode!`) for
  server-initiated messages.

## What accord adds that Phoenix (and h2spec-style tools) don't

The protocol model is **model-checked** (the lifecycle is proven sound) *and* run
as a **live blame-assigning monitor**, from one spec, on a protocol that had
neither. The monitor's value is concentrated where Phoenix deliberately does not
protect you — the reply obligation in your own channels — and in turning Phoenix's
lenient silent drops into visible, attributed diagnostics.
