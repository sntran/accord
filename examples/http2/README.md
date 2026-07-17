# HTTP/2 (RFC 9113)

Four **conformant** accord specs drawn from a real protocol — the HTTP/2 machinery
as implemented by [Bandit](https://github.com/mtrudel/bandit) — plus a live tap
proxy that wires the stream spec's runtime monitor between a real client and a
running Bandit server to **catch a real divergence in real time**.

This example is not a single tidy protocol. It is a set of related contracts that
exercise the parts of accord added for wire protocols (`cast`/`event` one-way
messages, `abstract: :monotonic` domains, `shared:` tracks, `const`), and it uses
accord two ways: TLC proves each spec is sound, and the runtime monitor — the same
IR, flowing downward — is placed in a live connection to detect where Bandit
departs from the spec. The full investigation is
[`docs/case-study-http2-bandit.md`](../../docs/case-study-http2-bandit.md).

## The four specs (all conformant)

| File | Models | RFC | TLC proves |
|------|--------|-----|------------|
| `stream.ex` | single-stream state machine | §5.1 | the frame FSM is reachable and deadlock-free |
| `stream_id.ex` | stream-ID monotonicity fence | §5.1.1 | no two streams share an ID |
| `flow_control.ex` | send-window accounting | §6.9.1 | the window never overflows its ceiling |
| `connection.ex` | GOAWAY gating new streams | §6.8 | no stream opens after GOAWAY |

None contains a seeded bug. `test/examples/http2_test.exs` model-checks all four
with real TLC (`assert_passes`).

## Live divergence detection

The headline: accord's monitors, placed between a client and Bandit, catch two
real RFC 9113 divergences in a running server and — the key point — blame the
**server** for each.

```
raw HTTP/2 client ── frames ──▶ [ TapProxy ] ── frames ──▶ Bandit
                                     │ (bytes forwarded verbatim)
                                     ├─▶ per-stream  Stream.Protocol monitor
                                     └─▶ connection  StreamIdMonitor.Protocol monitor
```

`TapProxy` (`tap_proxy.ex`) relays TCP bytes unchanged while parsing the HTTP/2
frame layer — just the 9-byte frame headers (type + END_STREAM flag + stream id),
no HPACK, which is exactly what the state machines dispatch on. Each stream frame
is fed to a per-stream monitor as a `cast` (client → server) or server-push
`event` (server → client); stream opens and connection-level frames feed one
connection-wide monitor. Because it watches live traffic, the specs model every
frame a conformant server legitimately sends (including server WINDOW_UPDATE), and
a header block split across HEADERS + CONTINUATION (§6.10) is assembled rather than
ignored — so a well-formed request, split headers and all, raises nothing. That
faithfulness is the first thing the tests assert.

**§8.1 — trailers without END_STREAM (server must reset).** The client ends the
body with a trailing HEADERS frame lacking END_STREAM, then more DATA. That frame
is a protocol error, so `stream.ex` routes the stream to `:reset_expected`, where
the only legal server frame is RST_STREAM. Bandit instead answers 200 and folds
the trailing DATA into the body (`"OKMORE"`) — so its response frames are
**server-blame** violations (expected `:s_rst_stream`).

**§5.1.1 — a lower stream id (server must GOAWAY).** A HEADERS on a stream id at
or below the high-water mark is a connection error. `stream_id_monitor.ex` uses a
`where:`-guarded **cast branch** to route that open to `:goaway_expected`, where
the server owes a connection GOAWAY. Bandit silently drops the frame and keeps
serving. Because that mishandling is *inaction*, the client provokes it with a
PING; Bandit's PING ACK arriving in `:goaway_expected` (instead of a GOAWAY) is
the **server-blame** violation. Catching a silent-drop bug this way — provoke,
then check the server is going away — is a general technique the passive-monitor
limit forces.

```bash
mix run examples/http2/demo.exs
```

```
== trailers without END_STREAM (RFC 9113 §8.1) ==
Bandit response body: "OKMORE"
error: server pushed an event not valid in state :reset_expected
    note: pushed :s_headers in state :reset_expected
    help: valid messages: :s_rst_stream

== lower stream id (RFC 9113 §5.1.1) ==
Bandit dropped the lower-id HEADERS and kept serving (it ACKed the PING).
error: server pushed an event not valid in state :goaway_expected
    note: pushed :ping_ack in state :goaway_expected
    help: valid messages: :goaway
```

## Files

| File | Purpose |
|------|---------|
| `stream.ex`, `stream_id.ex`, `flow_control.ex`, `connection.ex` | the four conformant specs |
| `stream_id_monitor.ex` | connection-level runtime monitor for §5.1.1 (uses a cast branch) |
| `tap_proxy.ex` | the frame-parsing TCP proxy that taps frames into the monitors |
| `raw_client.ex` | a minimal raw-frame h2c client (can send the malformed sequences) |
| `echo_server.ex` | a cleartext HTTP/2 Bandit echo server for the demo/test |
| `demo.exs` | runs a well-formed and two divergent exchanges through the proxy |
| `bandit_repro/` | reference probes that confirm the same bugs in Bandit's own test harness |

## Running it

```bash
# Model-check every spec (needs tla2tools.jar):
mix test test/examples/http2_test.exs --only tlc

# Live detection against a real Bandit (Bandit is a dev/test dependency):
mix test test/examples/http2_test.exs
mix run examples/http2/demo.exs
```

## Two other divergences

Two more runtime-confirmed Bandit divergences are wrong error codes, not state
transitions, so they live below the monitor and are documented in the case study
rather than caught by the proxy: a zero-increment WINDOW_UPDATE returns
FLOW_CONTROL_ERROR where §6.9 requires PROTOCOL_ERROR, and an out-of-range
MAX_FRAME_SIZE returns FRAME_SIZE_ERROR where §6.5.2 requires PROTOCOL_ERROR. The
§5.1.1 lower-stream-id drop and the §8.1 trailers absorption also have standalone
reference probes in [`bandit_repro/`](bandit_repro/) that confirm them directly in
Bandit's own test harness.

## What accord did and did not do

accord did not find these bugs automatically. Its value is the discipline of
writing the exact contract — the legal-frame-per-state table — and then *enforcing*
it live. The trailers divergence is a frame the spec's `:open` state does not
admit; feeding real traffic through the monitor surfaces the moment Bandit accepts
it anyway. The wrong-error-code divergences sit below that table (frame-value
validation), which is why the case study, not the proxy, carries them.
