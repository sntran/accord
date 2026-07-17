# Run with: mix run examples/circuit_breaker/demo.exs
#
# The breaker has three states:
#   closed    - passes requests through and counts consecutive failures
#   open      - rejects every request
#   half_open - lets a single probe request through
#
# It trips (closed -> open) after 3 failures in a row. This demo runs the
# normal flow, then shows one client mistake and one server mistake that
# the monitor catches.

alias Accord.Examples.CircuitBreaker.{MislabelingServer, Protocol, Server}
alias Accord.Monitor

{:ok, server} = Server.start_link()
{:ok, monitor} = Protocol.Monitor.start_link(upstream: server, violation_policy: :reject)

IO.puts("== normal operation: three failures trip the breaker, then it rejects ==")
Server.push_outcomes(server, [:error, :error, :error])
IO.inspect(Monitor.call(monitor, :request), label: "request 1 (fails)")
IO.inspect(Monitor.call(monitor, :request), label: "request 2 (fails)")
IO.inspect(Monitor.call(monitor, :request), label: "request 3 (fails, trips)")
IO.inspect(Monitor.call(monitor, :request), label: "request while open (rejected)")
IO.puts("(after a 30s cooldown the breaker moves to half_open on its own)")

IO.puts("\n== client mistake: a message the current state does not accept ==")

IO.puts(
  "In :open the only valid message is :request. Sending :force_reset is the client's fault."
)

{:accord_violation, violation} = Monitor.call(monitor, :force_reset)
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))

IO.puts("\n== server mistake: the wrong reply on the failure that should trip ==")

IO.puts(
  "On the third failure the server must reply :tripped. This server replies :error instead,"
)

IO.puts("which is only valid below the threshold — so the monitor blames the server.")
{:ok, bad_server} = MislabelingServer.start_link()
{:ok, bad_monitor} = Protocol.Monitor.start_link(upstream: bad_server, violation_policy: :reject)

IO.inspect(Monitor.call(bad_monitor, :request), label: "request 1 (fails)")
IO.inspect(Monitor.call(bad_monitor, :request), label: "request 2 (fails)")
{:accord_violation, violation} = Monitor.call(bad_monitor, :request)
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
