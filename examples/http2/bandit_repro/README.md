# Bandit reproduction probes

These two files reproduce, against a running Bandit server, the divergences the
HTTP/2 specs describe. They are **reference material** — accord takes no dependency
on Bandit, and nothing here runs as part of accord's own test suite. They were
confirmed against **Bandit 1.12.0**.

Each file is an ExUnit `test` written against Bandit's own HTTP/2 test harness
(`SimpleH2Client`), so the way to run them is to drop each `test` into Bandit's
`test/bandit/http2/protocol_test.exs` and run it there.

## Steps

```bash
git clone https://github.com/mtrudel/bandit /tmp/bandit
cd /tmp/bandit
git checkout v1.12.0   # or the version you want to check
mix deps.get
```

Open `test/bandit/http2/protocol_test.exs`. It already `use`s the test helpers and
defines the `/echo` and `/no_body_response` plugs these probes rely on. Paste the
`test` block from each file into any `describe` in that module, then run:

```bash
mix test test/bandit/http2/protocol_test.exs
```

## What each probe shows

- **`trailers_probe.exs`** (RFC 9113 §8.1) — sends DATA, then a trailing HEADERS
  frame *without* END_STREAM, then more DATA. On 1.12.0 the response body is
  `"OKMORE"`: the post-trailer bytes are folded into the request body and the
  stream completes with `200`. A compliant server rejects the unterminated
  trailers with a stream `PROTOCOL_ERROR` (RST_STREAM). This is the bug the
  `Stream.TrailersBug` spec models.

- **`lower_id_probe.exs`** (RFC 9113 §5.1.1) — opens and completes stream 3, then
  sends HEADERS on the lower stream 1. §5.1.1 requires a connection
  `PROTOCOL_ERROR` (GOAWAY); on 1.12.0 the frame is silently dropped and the
  connection stays alive. This is the rule the `StreamId.Protocol` spec fences.

Both are lenient-leaning divergences (no crash, no leak); `trailers_probe` is the
message-integrity one worth reporting. See
[`../../../docs/case-study-http2-bandit.md`](../../../docs/case-study-http2-bandit.md)
for the full analysis, RFC citations, and fixes.
