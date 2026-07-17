# Run with: mix run examples/payment/demo.exs
#
# A card payment goes through these steps:
#   authorize(n) - reserve up to n on the card
#   capture(n)   - take money; captures add up and must not exceed the authorization
#   finalize     - close captures; refunds are only allowed after this
#   refund(n)    - return money; refunds must not exceed what was captured
#
# This demo runs the normal flow, then shows two client mistakes the
# monitor catches.

alias Accord.Examples.Payment.{Protocol, Server}
alias Accord.Monitor

{:ok, server} = Server.start_link()
{:ok, monitor} = Protocol.Monitor.start_link(upstream: server, violation_policy: :reject)

IO.puts("== normal flow: authorize, two captures, finalize, refund ==")
IO.inspect(Monitor.call(monitor, {:authorize, 4}), label: "authorize(4)")
IO.inspect(Monitor.call(monitor, {:capture, 2}), label: "capture(2)")
IO.inspect(Monitor.call(monitor, {:capture, 2}), label: "capture(2), total 4 of 4")
IO.inspect(Monitor.call(monitor, :finalize), label: "finalize")
IO.inspect(Monitor.call(monitor, {:refund, 1}), label: "refund(1)")

IO.puts("\n== client mistake: capturing more than authorized ==")

IO.puts(
  "With 2 authorized, capturing 3 breaks the rule captured <= authorized — the client's fault."
)

{:ok, server2} = Server.start_link()
{:ok, monitor2} = Protocol.Monitor.start_link(upstream: server2, violation_policy: :reject)
IO.inspect(Monitor.call(monitor2, {:authorize, 2}), label: "authorize(2)")
{:accord_violation, violation} = Monitor.call(monitor2, {:capture, 3})
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))

IO.puts("\n== client mistake: refunding before finalizing ==")

IO.puts(
  "Refunds are only valid after finalize. Sending :refund while still authorized is the client's fault."
)

{:accord_violation, violation} = Monitor.call(monitor2, {:refund, 1})
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
