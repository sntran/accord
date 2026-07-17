# Case study: Phoenix Channels

A test of accord against a BEAM-native protocol chosen deliberately for the
property the HTTP/2 study lacked: **no conformance oracle exists.** HTTP/2 has
h2spec; the WebSocket layer has Autobahn; the Phoenix *channel* protocol — the
realtime transport under Phoenix Channels and LiveView — has neither. That makes
it the honest setting for accord's actual value, rather than a demo where a mature
specialized tool already does the job better.

## The protocol

Phoenix multiplexes many channels over one socket, keyed by topic (disambiguated
by `join_ref`). Each channel is an independent lifecycle. The wire format (v2) is a
JSON array `[join_ref, ref, topic, event, payload]`; `ref` correlates a server
reply (`phx_reply`) to the client request that carried it. Investigation of the
Phoenix source (`lib/phoenix/socket.ex`, `channel/server.ex`, the v2 serializer)
established the state machine and, more importantly, the **server obligations** —
including several the framework leaves unenforced.

## The model

`examples/phoenix_channels/channel.ex` is a conformant accord contract: a per-topic
FSM `not_joined → joining → joined → leaving → closed`, with client frames as
one-way `cast`s and server frames as server-push `event`s. The reply obligation is
a `pending` counter — a client message that carries a `ref` (join, push, leave)
increments it; a `phx_reply` decrements it, guarded by `pending > 0`. In TLC that
guard is the enabling condition of a conformant server (the lifecycle model-checks
sound); at runtime it is the checked obligation (a reply with nothing pending fails
it → server blame). Model-checked clean by TLC.

## The integration: one line

The monitor is a `Phoenix.Socket.Serializer` that wraps the real v2 serializer and
taps every struct in both directions. Turning it on in any Phoenix app is one line:

```elixir
socket "/socket", MySocket,
  websocket: [serializer: [{Accord.Examples.PhoenixChannels.Serializer, "~> 2.0.0"}]]
```

The serializer is below the channel layer and above the transport, so it is
transport-agnostic and sees exactly the protocol structs. A `Tap` holds one channel
monitor per topic and routes messages to it.

## What it catches (live, against a real Phoenix endpoint)

`test/examples/phoenix_channels_test.exs` drives a running endpoint with a raw
WebSocket client:

| Scenario | Verdict |
|----------|---------|
| normal join / push+reply / leave | no violations (faithful) |
| a channel that replies twice to one request | **server** blame (`guard_failed`) |
| a push before joining a topic | **client** blame (`invalid_message`) |
| a stale `join_ref` (Phoenix drops it silently) | **client** blame — silent drop made visible |
| a server-initiated push mid-session | no violation |

Two of these are the whole point:

1. **The reply obligation lives in *your* code.** Phoenix does not track
   "one reply per request." A `handle_in` that calls `reply/2` twice for one `ref`,
   or replies to a `ref` no client sent, violates the protocol and the framework
   does not stop it. `BuggyChannel` does exactly this (a naive double `reply/2`);
   the monitor catches the second reply as server blame, while a correct channel
   raises nothing. This is the class of bug real applications actually have.

2. **Silent failures become visible.** A stale `join_ref` — from a client that
   rejoined but kept an old ref — is **silently dropped** by Phoenix (socket.ex:815:
   no reply, no log, the message just vanishes). That is the archetypal "why did my
   events stop arriving?" bug. The tap records the join_ref at join and surfaces a
   stale message with blame.

## The point: value where there is no oracle

The HTTP/2 study ended on an honest deduction — h2spec finds Bandit's bugs better
than accord does, so on a protocol with a mature conformance tester accord is
largely redundant. Phoenix Channels is the complement:

- **No h2spec exists for it.** For the protocols people actually build — internal
  RPC, custom framings, and here the BEAM's own realtime transport — there is no
  specialized oracle to reach for. accord is a way to get checking machinery from a
  spec you write once.
- **It does two things a conformance suite does not.** It **model-checks the
  design** (the lifecycle is proven sound before any server exists), and it runs as
  a **live blame-assigning monitor** in production/test — the same IR, both
  directions. h2spec is a black-box tester of an existing server; it neither proves
  a design nor attributes blame on live traffic.
- **Its value concentrates where the framework can't help.** The reply obligation
  and join_ref discipline are precisely the rules Phoenix leaves to you or handles
  silently. A monitor derived from the protocol contract is the thing that checks
  them.

## Cross-implementation testing: the harness as a client conformance suite

The channel protocol has essentially **one server** (Phoenix), so there is no rival
server to differentially test — the HTTP/2 "point it at Bandit" move has no target
here. But it has **many independent clients** (phoenix.js, and in other languages
Swift/Kotlin/Rust/Dart/Python, plus the Elixir clients Slipstream and
PhoenixClient), and those reimplement the tricky parts — reply correlation, the
rejoin-after-error flow, join_ref discipline — with far less testing than Phoenix's
server. The instrumented endpoint is exactly a **conformance harness for a client
library**: point a client at it, and any `client`-blame violation is that client's
protocol bug.

The example demonstrates both halves against a real, third-party client:

- **The harness has teeth.** The raw-`WsClient` tests send sequences a real library
  refuses to — a push before join, a stale join_ref — and the monitor flags them as
  client blame. So a clean run is meaningful, not vacuous.
- **A conformant client passes clean.** [Slipstream](https://hexdocs.pm/slipstream)
  (an independent Elixir client, unrelated to the raw one) runs a normal session
  and two concurrent channels through the instrumented endpoint with **zero
  violations** — validating the monitor across a different implementation, and
  confirming Slipstream conforms. (Slipstream is conformant by construction in
  places: its `push/4` checks `joined?` and returns `{:error, :not_joined}` rather
  than sending a premature push.)

**No bug was found in Slipstream, and that is the honest expected result** — it is
mature and well-tested. The value here is the reusable harness and the
cross-implementation validation, not a headline finding. The richer hunting ground
is the less-maintained non-Elixir clients (a Swift/Kotlin/Rust client that mishandles
the rejoin-after-error join_ref update is exactly the bug class this catches) — but
each needs its own toolchain to drive, so they are targets this environment can
describe but not run. What the monitor can catch is limited to **wire** violations
(push before join, stale join_ref, sending after leave); a client's purely internal
bug — misrouting a correctly-delivered reply to the wrong pending request — happens
inside the client and never appears on the wire.

## Honest scope

- **Topic keying.** A channel's push replies are encoded in the channel process
  while its join reply is encoded in the connection process, so `self()` is not a
  stable per-connection key. Monitors are keyed by topic (one connection at a time
  per topic) — enough for the demo, not for concurrent connections sharing a topic.
- **join_ref discipline is runtime-only** (join_refs are arbitrary strings, not
  model-checkable) — enforced by the tap, not TLC.
- **Duplicate join is not modeled.** Re-joining an already-joined topic makes
  Phoenix evict the old channel and rejoin (with a `phx_close` for the old one). The
  duplicate `phx_join` is flagged (a client anti-pattern the JS client prevents),
  but the evict-and-rejoin sequence then produces a spurious follow-on violation.
  Modeling it cleanly needs a rejoin path; left as a known boundary.
- **fastlane broadcasts** are encoded once in the broadcasting process, so they are
  observed but not attributable to a connection; the demo uses `push/3` for
  server-initiated messages.

None of these is hidden by the demo — the faithfulness test asserts a normal
session is clean, and the scoped-out cases are documented rather than silently
avoided.
