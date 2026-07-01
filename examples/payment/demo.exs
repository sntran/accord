# Run with: mix run examples/payment/demo.exs

alias Accord.Examples.Payment.{Protocol, Server}
alias Accord.Monitor

{:ok, server} = Server.start_link()
{:ok, monitor} = Protocol.Monitor.start_link(upstream: server, violation_policy: :reject)

IO.puts("== happy path: authorize, partial captures, finalize, refund ==")
IO.inspect(Monitor.call(monitor, {:authorize, 4}), label: "authorize(4)")
IO.inspect(Monitor.call(monitor, {:capture, 2}), label: "capture(2)")
IO.inspect(Monitor.call(monitor, {:capture, 2}), label: "capture(2)")
IO.inspect(Monitor.call(monitor, :finalize), label: "finalize")
IO.inspect(Monitor.call(monitor, {:refund, 1}), label: "refund(1)")

IO.puts("\n== client blame: over-capturing ==")
{:ok, server2} = Server.start_link()
{:ok, monitor2} = Protocol.Monitor.start_link(upstream: server2, violation_policy: :reject)
IO.inspect(Monitor.call(monitor2, {:authorize, 2}), label: "authorize(2)")
{:accord_violation, violation} = Monitor.call(monitor2, {:capture, 3})
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))

IO.puts("\n== client blame: refund before finalize ==")
{:accord_violation, violation} = Monitor.call(monitor2, {:refund, 1})
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
