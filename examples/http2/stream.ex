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
     Bandit server (`Accord.Examples.Http2.TapProxy`), where it catches a real
     divergence and — this is the point — assigns it to the **server**.

  The monitor flags frames by direction: a client frame with no transition is
  client-blamed, a server frame with no transition server-blamed. On top of that,
  the spec models one *server obligation* explicitly. A trailing HEADERS frame
  without END_STREAM is a §8.1 protocol error; the only HEADERS legal after the
  request headers is a trailer that bears END_STREAM (`:headers_es`). Rather than
  treat the bare `:headers` as merely a bad client frame, `:open` routes it to
  `:reset_expected`, where the server MUST send RST_STREAM. When Bandit instead
  sends a normal response there, that response frame has no transition and is a
  **server-blame** `:invalid_message` — accord catching Bandit's mishandling
  directly, not inferring it from an out-of-band check. (Bandit folds the
  post-trailer DATA into the body and answers 200; a compliant server resets.)

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
    # Trailers: the only HEADERS legal after the request headers bears END_STREAM.
    cast :headers_es, goto: :remote_closed
    # A bare trailing HEADERS (no END_STREAM) is a §8.1 protocol error. It drives
    # the stream to :reset_expected, where the server owes a RST_STREAM.
    cast :headers, goto: :reset_expected
    cast :window_update, goto: :open
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :open
    event :s_headers_es, goto: :local_closed
    event :s_data, goto: :open
    event :s_data_es, goto: :local_closed
    event :s_window_update, goto: :open
    event :s_rst_stream, goto: :closed
  end

  # A protocol error has occurred on the stream. RFC 9113 §8.1: the server MUST
  # reset it. The only legal server frame here is RST_STREAM; any other server
  # frame — a normal response — has no transition and is a server-blame
  # violation. Trailing client frames are tolerated (self-loops) so they add no
  # noise: this state exists to judge the server's response.
  state :reset_expected do
    event :s_rst_stream, goto: :closed

    cast :data, goto: :reset_expected
    cast :data_es, goto: :reset_expected
    cast :headers, goto: :reset_expected
    cast :headers_es, goto: :reset_expected
    cast :window_update, goto: :reset_expected
    cast :rst_stream, goto: :closed
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
