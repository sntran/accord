# RFC 9113 §5.1.1 — HEADERS on a lower stream id.
#
# Reference probe. Not part of accord's test suite. Drop this `test` into
# Bandit's test/bandit/http2/protocol_test.exs (which defines SimpleH2Client and
# the /no_body_response plug) and run it there. Confirmed against Bandit 1.12.0.
#
# A newly opened stream's id MUST be numerically greater than every stream the
# peer has already opened; an unexpected (lower) id MUST be a connection
# PROTOCOL_ERROR (GOAWAY). Bandit classifies a lower, never-opened id as :closed
# and drops the frame silently — the connection stays alive.
#
# Observed on 1.12.0: connection_alive?/1 returns true after the lower-id HEADERS.
# A compliant server would send a GOAWAY and close.

@tag :capture_log
test "HEADERS on a lower stream id is silently dropped (RFC 9113 §5.1.1)", context do
  socket = SimpleH2Client.setup_connection(context)

  # Open and complete stream 3 (the connection's last_stream_id becomes 3).
  {:ok, ctx} =
    SimpleH2Client.send_simple_headers(socket, 3, :get, "/no_body_response", context.port)

  assert SimpleH2Client.successful_response?(socket, 3, false)
  assert {:ok, 3, true, ""} = SimpleH2Client.recv_body(socket)

  # HEADERS on the lower stream 1. §5.1.1 requires a connection error.
  SimpleH2Client.send_simple_headers(socket, 1, :get, "/no_body_response", context.port, ctx)

  # Current (divergent) behavior: the frame is dropped and the connection lives.
  assert SimpleH2Client.connection_alive?(socket)

  # A compliant server would instead GOAWAY and close:
  #   assert {:ok, _last, 1} = SimpleH2Client.recv_goaway_and_close(socket)   # 1 = PROTOCOL_ERROR
end
