# HTTP/2 (RFC 9113)

Four accord specs drawn from a real protocol: the HTTP/2 machinery as implemented
by [Bandit](https://github.com/mtrudel/bandit). Unlike the other examples, this
one is not a single tidy protocol — it is a set of related contracts that together
exercise the parts of accord added for wire protocols (`cast`/`event` one-way
messages, `abstract: :monotonic` domains, `shared:` tracks, `const`). Each spec
model-checks clean, and each ships a seeded-bug variant that mirrors a
runtime-confirmed divergence in Bandit 1.12.0. The full investigation is
[`docs/case-study-http2-bandit.md`](../../docs/case-study-http2-bandit.md).

## The four specs

| File | Models | RFC | Seeded bug → Bandit finding |
|------|--------|-----|------------------------------|
| `stream.ex` | single-stream state machine | §5.1 | trailers without END_STREAM absorbed into the body (§8.1) |
| `stream_id.ex` | stream-ID monotonicity fence | §5.1.1 | two streams sharing an ID (guard dropped) |
| `flow_control.ex` | send-window accounting | §6.9.1 | window overflows its ceiling (guard dropped) |
| `connection.ex` | GOAWAY gating new streams | §6.8 | a stream opens after GOAWAY (gate dropped) |

## What the specs declare

- **`stream.ex`** — the stream FSM (idle → open → half-closed → closed). Frames are
  one-way in both directions, so peer frames are `cast`s and the server's frames
  are server-push `event`s. Each state lists exactly the frames legal in it; a
  frame with no listed transition is an `:invalid_message` protocol error. Two
  ghost booleans state the trailers-integrity property.
- **`stream_id.ex`** — two streams as `sessions: 2` sharing the connection's
  `last_id`. Each claims an ID strictly greater than `last_id`; `distinct :my_id`
  asserts uniqueness. `last_id` is `abstract: :monotonic` so the small model
  domain does not deadlock once the id space is "used up".
- **`flow_control.ex`** — the server's send window as a bounded track. The peer's
  WINDOW_UPDATE (`cast`) grows it under a `const :max` ceiling; the server's DATA
  (`event`) shrinks it. The invariant is that it never overflows.
- **`connection.ex`** — a connection-level `shared:` state gates per-session
  streams. A `cast :goaway` flips it; the open guard reads it. This is
  connection/stream composition with no dedicated two-level construct.

## The seeded bugs

Each `*.ex` file defines a correct `Protocol` and a bug variant (`TrailersBug`,
`Unguarded`) using `tla: :off` so `mix accord.check` stays green. The bug variants
are pinned by real TLC runs in `test/examples/http2_test.exs`:

- **`Stream.TrailersBug`** adds the one transition the correct table omits — a bare
  trailing `cast :headers` (no END_STREAM) in `:open` that does not terminate the
  stream. Then DATA follows the trailers and `data_after_trailers` becomes true.
  This is exactly what Bandit accepts; a compliant server sends a PROTOCOL_ERROR.
- **`StreamId.Unguarded`** drops the `id > last_id` guard; TLC finds two streams
  claiming the same ID.
- **`FlowControl.Unguarded`** drops the `send_window + inc <= max` guard; TLC finds
  the window past its ceiling in two states.
- **`Connection.Unguarded`** drops the `conn_state == :active` check; TLC finds a
  stream opening after GOAWAY.

## Running it

```bash
# Model-check every spec and its seeded bug (needs tla2tools.jar):
mix test test/examples/http2_test.exs --only tlc

# Runtime: the monitor validating a live stream FSM, with blame:
mix run examples/http2/demo.exs
```

## Reproducing the Bandit bugs

The two divergences that were confirmed against a running Bandit — the lower
stream-ID drop (§5.1.1) and the trailers-without-END_STREAM absorption (§8.1) —
have standalone reference probes in [`bandit_repro/`](bandit_repro/). They are not
wired into this project (accord takes no dependency on Bandit); the README there
explains how to drop them into a Bandit checkout and run them.

## What accord did and did not do

accord did not find these bugs automatically. Its value here was as a forcing
function: writing the exact legal-frame-per-state table made the stream FSM's
missing and extra transitions legible on a read (findings §5.1.1 and §8.1), and
writing an error-per-rejection column surfaced two wrong error codes (§6.9, §6.5.2,
covered in the case study). The overflow, id-uniqueness, and GOAWAY-gating
properties it does check mechanically — the seeded-bug tests prove that.
