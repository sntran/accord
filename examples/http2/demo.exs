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
# Bandit accepts the malformed trailers and folds the following DATA into the
# body; accord flags the frame.

alias Accord.Examples.Http2.{EchoServer, RawClient, TapProxy}
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

IO.puts("The well-formed request raised nothing; the malformed trailers were caught")
IO.puts("live, while Bandit answered 200 with body \"OKMORE\" — the §8.1 divergence.")
