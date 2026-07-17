# RFC 9113 §8.1 — trailers without END_STREAM.
#
# Reference probe. Not part of accord's test suite. Drop this `test` into
# Bandit's test/bandit/http2/protocol_test.exs (which defines SimpleH2Client and
# the /echo plug) and run it there. Confirmed against Bandit 1.12.0.
#
# A trailing HEADERS frame — the only HEADERS allowed after the request headers —
# must bear END_STREAM; it terminates the stream. Bandit accepts one without
# END_STREAM, leaves the stream open, and folds subsequent DATA into the body.
#
# Observed on 1.12.0: the response body is "OKMORE" — the post-trailer "MORE" was
# absorbed as body, with a normal 200 and no RST_STREAM. A compliant server sends
# RST_STREAM with PROTOCOL_ERROR at the unterminated trailers.

@tag :capture_log
test "trailers without END_STREAM are absorbed into the body (RFC 9113 §8.1)", context do
  socket = SimpleH2Client.setup_connection(context)

  {:ok, ctx} = SimpleH2Client.send_simple_headers(socket, 1, :post, "/echo", context.port)
  SimpleH2Client.send_body(socket, 1, false, "OK")

  {:ok, 0, _} = SimpleH2Client.recv_window_update(socket)
  {:ok, 1, _} = SimpleH2Client.recv_window_update(socket)

  # Trailing HEADERS WITHOUT END_STREAM, then more DATA that closes the stream.
  SimpleH2Client.send_headers(socket, 1, false, [{"x-trailer", "t"}], ctx)
  SimpleH2Client.send_body(socket, 1, true, "MORE")

  # Current (divergent) behavior: a normal 200 whose echoed body is "OKMORE".
  assert SimpleH2Client.successful_response?(socket, 1, false)
  assert {:ok, 1, true, "OKMORE"} = SimpleH2Client.recv_body(socket)

  # A compliant server would instead reset the stream:
  #   assert {:ok, 1, 1} = SimpleH2Client.recv_rst_stream(socket)   # code 1 = PROTOCOL_ERROR
end
