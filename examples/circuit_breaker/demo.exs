# Run with: mix run examples/circuit_breaker/demo.exs
#
# Trips the breaker through the monitor, then shows the two blame
# stories: a client sending an unknown message, and a server mislabeling
# the tripping failure. (The 30s cooldown then fires on its own — the
# state_timeout test exercises that with a short timer.)

alias Accord.Examples.CircuitBreaker.{MislabelingServer, Protocol, Server}
alias Accord.Monitor

{:ok, server} = Server.start_link()
{:ok, monitor} = Protocol.Monitor.start_link(upstream: server, violation_policy: :reject)

IO.puts("== happy path: trip, reject ==")
Server.push_outcomes(server, [:error, :error, :error])
IO.inspect(Monitor.call(monitor, :request), label: "request 1")
IO.inspect(Monitor.call(monitor, :request), label: "request 2")
IO.inspect(Monitor.call(monitor, :request), label: "request 3 (trips)")
IO.inspect(Monitor.call(monitor, :request), label: "request while open")
IO.puts("(the breaker probes on its own after the 30s cooldown)")

IO.puts("\n== client blame: unknown message ==")
{:accord_violation, violation} = Monitor.call(monitor, :force_reset)
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))

IO.puts("\n== server blame: mislabeling the tripping failure ==")
{:ok, bad_server} = MislabelingServer.start_link()
{:ok, bad_monitor} = Protocol.Monitor.start_link(upstream: bad_server, violation_policy: :reject)

IO.inspect(Monitor.call(bad_monitor, :request), label: "request 1")
IO.inspect(Monitor.call(bad_monitor, :request), label: "request 2")
{:accord_violation, violation} = Monitor.call(bad_monitor, :request)
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
