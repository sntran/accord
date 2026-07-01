# Run with: mix run examples/genstage_demand/demo.exs

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

IO.puts("== happy path: ask, then events arrive within demand ==")
IO.inspect(Monitor.call(monitor, {:ask, 3}), label: "ask(3)")
IO.inspect(Producer.emit(producer, 2), label: "emit(2)")

receive do
  {:events, n} -> IO.puts("consumer received {:events, #{n}}")
end

IO.puts("\n== server blame: an over-eager producer ==")
{:ok, eager} = OverEagerProducer.start_link()

{:ok, monitor2} =
  Protocol.Monitor.start_link(
    upstream: eager,
    downstream: self(),
    violation_policy: :log
  )

OverEagerProducer.attach_monitor(eager, monitor2)

IO.inspect(Monitor.call(monitor2, {:ask, 1}), label: "ask(1)")
# Pushes 3 events against demand of 1 — the guard is the documented rule.
OverEagerProducer.emit(eager, 3)
:sys.get_state(monitor2)
Process.sleep(50)
