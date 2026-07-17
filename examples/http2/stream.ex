defmodule Accord.Examples.Http2.Stream.Protocol do
  @moduledoc """
  HTTP/2 single-stream state machine (RFC 9113 §5.1), from the Bandit case study
  (`docs/case-study-http2-bandit.md`).

  A stream moves through idle → open → half-closed → closed. Frames are one-way in
  both directions, so peer frames are `cast`s (client → server) and the server's
  own frames are server-push `event`s — no request/reply. END_STREAM is a flag on
  DATA and HEADERS; since accord dispatches by message tag, each carrier splits
  into a plain tag and an `_es` tag (`:data`/`:data_es`, `:headers_es`).

  The legal-frame-per-state table is the whole point: each state lists exactly the
  frames that may arrive in it. A frame with no matching transition is an
  `:invalid_message` protocol error at runtime and simply has no action in the
  model. Two ghost booleans (`trailers_seen`, `data_after_trailers`) let us state
  the trailers-integrity property that the seeded bug violates; see
  `Accord.Examples.Http2.Stream.TrailersBug`.
  """
  use Accord.Protocol

  initial :idle

  # Ghost bookkeeping for the trailers property. `trailers_seen` becomes true only
  # on a stream-terminating trailer (`headers_es`), so in a correct stream no DATA
  # can ever follow it — `data_after_trailers` stays false.
  track :trailers_seen, :boolean, default: false
  track :data_after_trailers, :boolean, default: false

  # A request begins with HEADERS. With END_STREAM it is a bodyless request and
  # the peer half-closes immediately.
  state :idle do
    cast :headers, goto: :open
    cast :headers_es, goto: :remote_closed
  end

  # Peer may stream DATA, then either a terminating DATA (END_STREAM) or trailers
  # (a HEADERS that bears END_STREAM). The server pushes its response as events.
  state :open do
    cast :data, goto: :open

    cast :data_es do
      goto :remote_closed
    end

    # Trailers: the only HEADERS legal after the request headers, and it MUST bear
    # END_STREAM (it terminates the stream). Records that trailers have been seen.
    cast :headers_es do
      goto :remote_closed
      update fn _msg, tracks -> %{tracks | trailers_seen: true} end
    end

    cast :window_update, goto: :open
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :open
    event :s_headers_es, goto: :local_closed
    event :s_data, goto: :open
    event :s_data_es, goto: :local_closed
  end

  # Peer has half-closed (END_STREAM seen). It may still manage flow/reset; the
  # server may still push its response. Peer DATA or a bare HEADERS here has no
  # transition — an invalid frame.
  state :remote_closed do
    cast :window_update, goto: :remote_closed
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :remote_closed
    event :s_headers_es, goto: :closed
    event :s_data, goto: :remote_closed
    event :s_data_es, goto: :closed
  end

  # Server has sent END_STREAM; the peer may still send its request body.
  state :local_closed do
    cast :data, goto: :local_closed
    cast :data_es, goto: :closed
    cast :headers_es, goto: :closed
    cast :window_update, goto: :local_closed
    cast :rst_stream, goto: :closed
  end

  state :closed, terminal: true

  # No DATA is ever accepted after the trailers boundary. A correct stream cannot
  # reach a state where trailers were seen but the stream still takes DATA, so
  # this holds; the seeded bug breaks it.
  property :no_data_after_trailers do
    forbidden fn tracks -> tracks.data_after_trailers end
  end
end

defmodule Accord.Examples.Http2.Stream.TrailersBug do
  @moduledoc """
  Seeded bug matching a real Bandit divergence (RFC 9113 §8.1, case study round 3):
  a trailing HEADERS frame that lacks END_STREAM is accepted and leaves the stream
  open, so subsequent DATA is folded into the request body.

  This adds the one transition the correct table omits — a bare `cast :headers`
  in `:open` that does not terminate the stream — exactly what Bandit's
  `do_recv_end_stream(stream, false)` implements as a silent self-loop. With it,
  the peer can send HEADERS (no END_STREAM) then DATA, and `data_after_trailers`
  becomes true. TLC finds the two-frame counterexample; a compliant server rejects
  the unterminated trailers with a stream PROTOCOL_ERROR.
  """
  use Accord.Protocol, tla: :off

  initial :idle

  track :trailers_seen, :boolean, default: false
  track :data_after_trailers, :boolean, default: false

  state :idle do
    cast :headers, goto: :open
    cast :headers_es, goto: :remote_closed
  end

  state :open do
    # BUG: a bare trailing HEADERS (no END_STREAM) that does not terminate the
    # stream. RFC 9113 §8.1 requires a PROTOCOL_ERROR here.
    cast :headers do
      goto :open
      update fn _msg, tracks -> %{tracks | trailers_seen: true} end
    end

    # DATA now records whether it arrived after the (unterminated) trailers.
    cast :data do
      goto :open
      update fn _msg, tracks -> %{tracks | data_after_trailers: tracks.trailers_seen} end
    end

    cast :data_es, goto: :remote_closed

    cast :headers_es do
      goto :remote_closed
      update fn _msg, tracks -> %{tracks | trailers_seen: true} end
    end

    cast :window_update, goto: :open
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :open
    event :s_headers_es, goto: :local_closed
    event :s_data, goto: :open
    event :s_data_es, goto: :local_closed
  end

  state :remote_closed do
    cast :window_update, goto: :remote_closed
    cast :rst_stream, goto: :closed

    event :s_headers, goto: :remote_closed
    event :s_headers_es, goto: :closed
    event :s_data, goto: :remote_closed
    event :s_data_es, goto: :closed
  end

  state :local_closed do
    cast :data, goto: :local_closed
    cast :data_es, goto: :closed
    cast :headers_es, goto: :closed
    cast :window_update, goto: :local_closed
    cast :rst_stream, goto: :closed
  end

  state :closed, terminal: true

  property :no_data_after_trailers do
    forbidden fn tracks -> tracks.data_after_trailers end
  end
end
