# Run with: mix run examples/http2/demo.exs
#
# accord as a live conformance monitor. A tap proxy sits between a raw HTTP/2
# client and a real, running Bandit server, forwarding bytes verbatim while
# feeding each frame into the accord stream-state-machine monitor. When a frame
# does not fit the RFC state machine, accord records a violation — catching a real
# divergence in the server, in real time.
#
# Two requests are sent through the proxy: a well-formed one (which must produce
# no violations, proving the monitor is faithful to real traffic), and one that
# ends the body with a trailing HEADERS frame lacking END_STREAM (RFC 9113 §8.1).
# That frame is a protocol error; §8.1 requires the server to reset the stream.
# Bandit instead answers 200 and folds the following DATA into the body — so
# accord, expecting a RST_STREAM, blames the SERVER for the response frames it
# sends. accord catches Bandit's mishandling directly, not by inspecting the body.

alias Accord.Examples.Http2.{EchoServer, RawClient, StreamIdMonitor, TapProxy}
alias Accord.Examples.Http2.Stream.Protocol
alias Accord.Test.ViolationCollector

{:ok, _server, bandit_port} = EchoServer.start_link()
IO.puts("Bandit (h2c echo) listening on port #{bandit_port}\n")

run = fn label, frames ->
  ViolationCollector.init()
  {:ok, proxy} = TapProxy.start_link(bandit_port)
  port = TapProxy.port(proxy)

  conn = RawClient.connect(port)
  conn = Enum.reduce(frames, conn, fn f, c -> f.(c, port) end)
  body = RawClient.read_body(conn)
  violations = TapProxy.violations(proxy)

  IO.puts("== #{label} ==")
  IO.puts("Bandit response body: #{inspect(body)}")

  case violations do
    [] ->
      IO.puts("accord: no violations — the traffic conformed to the spec.\n")

    list ->
      IO.puts("accord flagged #{length(list)} violation(s):")

      for v <- list do
        IO.puts(Accord.Violation.Report.format(v, Protocol.__compiled__()))
      end

      IO.puts("")
  end
end

run.("well-formed request", [
  fn c, port -> RawClient.post_echo(c, 1, false, port) end,
  fn c, _ -> RawClient.data(c, 1, true, "OK") end
])

run.("trailers without END_STREAM (RFC 9113 §8.1)", [
  fn c, port -> RawClient.post_echo(c, 1, false, port) end,
  fn c, _ -> RawClient.data(c, 1, false, "OK") end,
  # The divergent frame: a trailing HEADERS with no END_STREAM.
  fn c, _ -> RawClient.headers(c, 1, false, [{"x-trailer", "t"}]) end,
  fn c, _ -> RawClient.data(c, 1, true, "MORE") end
])

# A lower stream id (§5.1.1) is a connection-level rule, watched by a separate
# connection monitor. Bandit's mishandling here is silent (it drops the frame),
# so we provoke it with a PING: a going-away server would not answer normally.
ViolationCollector.init()
{:ok, proxy} = TapProxy.start_link(bandit_port)
port = TapProxy.port(proxy)

conn = RawClient.connect(port)
conn = conn |> RawClient.post_echo(3, false, port) |> RawClient.data(3, true, "x")
_ = RawClient.read_body(conn)
# HEADERS on the lower stream 1 — a §5.1.1 protocol error — then a PING probe.
conn = conn |> RawClient.post_echo(1, false, port) |> RawClient.ping()
:ok = RawClient.await_ping_ack(conn)

IO.puts("== lower stream id (RFC 9113 §5.1.1) ==")
IO.puts("Bandit dropped the lower-id HEADERS and kept serving (it ACKed the PING).")

for v <- TapProxy.violations(proxy) do
  IO.puts(Accord.Violation.Report.format(v, StreamIdMonitor.Protocol.__compiled__()))
end

IO.puts("""

The well-formed request raised nothing. In both divergent cases accord blamed the
SERVER, live: on the §8.1 trailers Bandit answered 200 (body "OKMORE") where it
owed a reset; on the §5.1.1 lower id it kept serving where it owed a GOAWAY. The
latter is a silent mishandling, so the PING provokes an observable response.\
""")
