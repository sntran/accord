# Run with: mix run examples/job_queue/demo.exs
#
# A worker leases a job from the queue:
#   checkout          - take a job; the queue replies {:job, token}
#   heartbeat(token)  - keep the lease; must present the current token
#   ack(token)        - finish the job; must present the current token
#   the queue can push {:lease_expired, token} when a lease times out
#
# Each checkout must return a token strictly larger than any before it (a
# fencing token), so a lost lease can never be confused with a current one.
# This demo runs the normal flow, then shows one client mistake and one
# server mistake.

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

IO.puts("== normal flow: checkout, heartbeat, ack ==")
IO.inspect(Monitor.call(monitor, :checkout), label: "checkout (gets token 1)")
IO.inspect(Monitor.call(monitor, {:heartbeat, 1}), label: "heartbeat(1)")
IO.inspect(Monitor.call(monitor, {:ack, 1}), label: "ack(1)")

IO.puts("\n== the queue pushes a lease-expired event when a lease times out ==")
IO.inspect(Monitor.call(monitor, :checkout), label: "checkout (gets token 2)")
Server.expire_lease(queue)

receive do
  {:lease_expired, token} -> IO.puts("worker received {:lease_expired, #{token}}")
after
  500 -> IO.puts("no expiry received!")
end

IO.puts("\n== client mistake: acking after the lease expired ==")

IO.puts(
  "The expiry returned the worker to :idle, where :ack is not a valid message — the client's fault."
)

{:accord_violation, violation} = Monitor.call(monitor, {:ack, 2})
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))

IO.puts("\n== server mistake: reissuing a fence token instead of increasing it ==")

IO.puts(
  "Each checkout must return a larger token. This queue hands out token 1 again — the server's fault."
)

{:ok, bad_queue} = StaleTokenServer.start_link()
{:ok, bad_monitor} = Protocol.Monitor.start_link(upstream: bad_queue, violation_policy: :reject)

IO.inspect(Monitor.call(bad_monitor, :checkout), label: "checkout (gets token 1)")
IO.inspect(Monitor.call(bad_monitor, {:ack, 1}), label: "ack(1)")
{:accord_violation, violation} = Monitor.call(bad_monitor, :checkout)
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
