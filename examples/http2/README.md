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

The headline: `stream.ex`'s monitor, placed between a client and Bandit, catches
the RFC 9113 §8.1 trailers divergence in a running server.

```
raw HTTP/2 client ── frames ──▶ [ TapProxy ] ── frames ──▶ Bandit
                                     │ (bytes forwarded verbatim)
                                     ▼
                          per-stream Stream.Protocol monitor
                                     │
                     flags a bare trailing HEADERS (no END_STREAM) in :open
```

`TapProxy` (`tap_proxy.ex`) relays TCP bytes unchanged while parsing the HTTP/2
frame layer — just the 9-byte frame headers (type + END_STREAM flag + stream id),
no HPACK, which is exactly what the stream machine dispatches on. Each stream
frame is fed to a per-stream monitor as a `cast` (client → server) or server-push
`event` (server → client). Because it monitors live traffic, `stream.ex` models
every frame a conformant server legitimately sends (including server
WINDOW_UPDATE), so a well-formed request raises nothing — that faithfulness is the
first thing the test asserts.

Then the client sends a trailing HEADERS frame **without** END_STREAM and more
DATA after it. Bandit accepts the malformed trailers and folds the trailing DATA
into the request body (`"OKMORE"`); accord flags the frame, because the only
HEADERS legal after the request headers is a trailer that bears END_STREAM
(`:headers_es`) — a bare `:headers` has no transition in `:open`. A compliant
server would reset the stream with a PROTOCOL_ERROR (§8.1).

```bash
mix run examples/http2/demo.exs
```

```
== well-formed request ==
Bandit response body: "OK"
accord: no violations — the traffic conformed to the spec.

== trailers without END_STREAM (RFC 9113 §8.1) ==
Bandit response body: "OKMORE"
accord flagged 1 violation(s):
error: message not valid in state :open
    note: sent :headers in state :open
    help: valid messages: :data, :data_es, :headers_es, :rst_stream, …
```

## Files

| File | Purpose |
|------|---------|
| `stream.ex`, `stream_id.ex`, `flow_control.ex`, `connection.ex` | the four conformant specs |
| `tap_proxy.ex` | the frame-parsing TCP proxy that taps frames into per-stream monitors |
| `raw_client.ex` | a minimal raw-frame h2c client (can send the malformed sequences) |
| `echo_server.ex` | a cleartext HTTP/2 Bandit echo server for the demo/test |
| `demo.exs` | runs a well-formed and a divergent request through the proxy |
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
