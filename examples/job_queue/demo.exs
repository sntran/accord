# Run with: mix run examples/job_queue/demo.exs

alias Accord.Examples.JobQueue.{Protocol, Server, StaleTokenServer}
alias Accord.Monitor

{:ok, queue} = Server.start_link()

{:ok, monitor} =
  Protocol.Monitor.start_link(
    upstream: queue,
    downstream: self(),
    violation_policy: :reject
  )

Server.attach_monitor(queue, monitor)

IO.puts("== happy path: checkout, heartbeat, ack ==")
IO.inspect(Monitor.call(monitor, :checkout), label: "checkout")
IO.inspect(Monitor.call(monitor, {:heartbeat, 1}), label: "heartbeat(1)")
IO.inspect(Monitor.call(monitor, {:ack, 1}), label: "ack(1)")

IO.puts("\n== the visibility timeout arrives as a server event ==")
IO.inspect(Monitor.call(monitor, :checkout), label: "checkout")
Server.expire_lease(queue)

receive do
  {:lease_expired, token} -> IO.puts("worker received {:lease_expired, #{token}}")
after
  500 -> IO.puts("no expiry received!")
end

IO.puts("\n== client blame: acking with a stale token ==")
{:accord_violation, violation} = Monitor.call(monitor, {:ack, 2})
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))

IO.puts("\n== server blame: a queue that re-issues fence tokens ==")
{:ok, bad_queue} = StaleTokenServer.start_link()
{:ok, bad_monitor} = Protocol.Monitor.start_link(upstream: bad_queue, violation_policy: :reject)

IO.inspect(Monitor.call(bad_monitor, :checkout), label: "checkout")
IO.inspect(Monitor.call(bad_monitor, {:ack, 1}), label: "ack(1)")
{:accord_violation, violation} = Monitor.call(bad_monitor, :checkout)
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
