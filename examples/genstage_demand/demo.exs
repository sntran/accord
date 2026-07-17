# Run with: mix run examples/genstage_demand/demo.exs
#
# A consumer and producer follow the GenStage demand rule:
#   ask(n)     - the consumer asks for up to n events (increases demand)
#   the producer pushes {:events, n} - but must never send more than the
#   outstanding demand
#
# This demo runs the normal flow, then shows a producer that over-delivers.

alias Accord.Examples.Demand.{OverEagerProducer, Producer, Protocol}
alias Accord.Monitor

{:ok, producer} = Producer.start_link()

{:ok, monitor} =
  Protocol.Monitor.start_link(
    upstream: producer,
    downstream: self(),
    violation_policy: :reject
  )

Producer.attach_monitor(producer, monitor)

IO.puts("== normal flow: ask for 3, producer emits 2 (within demand) ==")
IO.inspect(Monitor.call(monitor, {:ask, 3}), label: "ask(3)")
IO.inspect(Producer.emit(producer, 2), label: "emit(2)")

receive do
  {:events, n} -> IO.puts("consumer received {:events, #{n}}")
end

IO.puts("\n== server mistake: emitting more events than demanded ==")

IO.puts(
  "Demand is 1, but this producer pushes 3 events. Over-delivery is the producer's (server's) fault."
)

{:ok, eager} = OverEagerProducer.start_link()

{:ok, monitor2} =
  Protocol.Monitor.start_link(
    upstream: eager,
    downstream: self(),
    violation_policy: :log
  )

OverEagerProducer.attach_monitor(eager, monitor2)

IO.inspect(Monitor.call(monitor2, {:ask, 1}), label: "ask(1)")
OverEagerProducer.emit(eager, 3)
:sys.get_state(monitor2)
Process.sleep(50)
