defmodule Accord.Examples.Http2.Stream.Protocol do
  @moduledoc """
  HTTP/2 single-stream state machine (RFC 9113 §5.1), from the Bandit case study
  (`docs/case-study-http2-bandit.md`).

  A stream moves through idle → open → half-closed → closed. Frames are one-way in
  both directions, so peer frames are `cast`s (client → server) and the server's
  own frames are server-push `event`s — no request/reply. END_STREAM is a flag on
  DATA and HEADERS; since accord dispatches by message tag, each carrier splits
  into a plain tag and an `_es` tag (`:data`/`:data_es`, `:headers_es`).

  This spec is **conformant** — it is the correct RFC behavior, with no seeded
  bug. It is used two ways:

  1. Model-checked by TLC (`test/examples/http2_test.exs`) to prove the state
     graph is sound (reachable, deadlock-free).
  2. Wired as a live runtime monitor between a real HTTP/2 client and a running
     Bandit server (`Accord.Examples.Http2.TapProxy`), where it flags frames
     Bandit mishandles. The key divergence it catches: a trailing HEADERS frame
     without END_STREAM in `:open`. That frame has no transition here — the only
     HEADERS legal after the request headers is a trailer that bears END_STREAM
     (`:headers_es`) — so the monitor reports an `:invalid_message`, while Bandit
     accepts it and folds subsequent DATA into the body (§8.1).

  Because it monitors *live* traffic, the state machine must accept every frame a
  conformant server legitimately sends — notably server WINDOW_UPDATE
  (`:s_window_update`), which Bandit emits to replenish the client's send window.
  A frame the spec omits would be a false positive on good traffic; the headline
  test asserts a normal request produces zero violations.
  """
  use Accord.Protocol

  initial :idle

  # A request begins with HEADERS. With END_STREAM it is a bodyless request and
  # the peer half-closes immediately.
  state :idle do
    cast :headers, goto: :open
    cast :headers_es, goto: :remote_closed
  end

  # Both peers may still send: the client streams its body, the server streams its
  # response, and either side manages flow control or resets.
  state :open do
    cast :data, goto: :open
    cast :data_es, goto: :remote_closed
    # Trailers: the only HEADERS legal after the request headers, and it MUST bear
    # END_STREAM. A bare :headers (no END_STREAM) has no transition here — that is
    # the §8.1 divergence the live monitor catches.
    cast :headers_es, goto: :remote_closed
    cast :window_update, goto: :open
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :open
    event :s_headers_es, goto: :local_closed
    event :s_data, goto: :open
    event :s_data_es, goto: :local_closed
    event :s_window_update, goto: :open
    event :s_rst_stream, goto: :closed
  end

  # Peer has half-closed (its END_STREAM seen). It may still manage flow/reset;
  # the server may still stream its response.
  state :remote_closed do
    cast :window_update, goto: :remote_closed
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :remote_closed
    event :s_headers_es, goto: :closed
    event :s_data, goto: :remote_closed
    event :s_data_es, goto: :closed
    event :s_window_update, goto: :remote_closed
    event :s_rst_stream, goto: :closed
  end

  # Server has half-closed; the peer may still stream its request body.
  state :local_closed do
    cast :data, goto: :local_closed
    cast :data_es, goto: :closed
    cast :headers_es, goto: :closed
    cast :window_update, goto: :local_closed
    cast :rst_stream, goto: :closed

    event :s_window_update, goto: :local_closed
    event :s_rst_stream, goto: :closed
  end

  state :closed, terminal: true
end
