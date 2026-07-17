# Run with: mix run examples/http2/demo.exs
#
# The HTTP/2 stream state machine, driven through the accord monitor. Frames are
# one-way messages (`cast` from the peer, server-push `event` from the server), so
# the monitor validates each frame against the current state and assigns blame —
# the same monitor that fronts request/reply protocols, now applied to a frame
# protocol. This demo runs a legal frame sequence, then one illegal frame the
# monitor rejects with client blame.

alias Accord.Examples.Http2.Stream.Protocol
alias Accord.Monitor
alias Accord.Test.ViolationCollector

defmodule DemoUpstream do
  @moduledoc "A no-op upstream: forwarded frames are simply accepted."
  use GenServer

  def start_link, do: GenServer.start_link(__MODULE__, nil)
  def init(state), do: {:ok, state}
  def handle_cast(_message, state), do: {:noreply, state}
  def handle_call(_message, _from, state), do: {:reply, :ok, state}
end

ViolationCollector.init()
{:ok, server} = DemoUpstream.start_link()

{:ok, monitor} =
  Protocol.Monitor.start_link(
    upstream: server,
    downstream: self(),
    violation_policy: {ViolationCollector, :handle}
  )

IO.puts("== a legal frame sequence advances the stream ==")
IO.puts("HEADERS opens the stream, DATA streams the body, DATA+END_STREAM half-closes it.")

Monitor.cast(monitor, :headers)
{state, _} = :sys.get_state(monitor)
IO.inspect(state, label: "after HEADERS")

Monitor.cast(monitor, :data)
{state, _} = :sys.get_state(monitor)
IO.inspect(state, label: "after DATA")

Monitor.cast(monitor, :data_es)
{state, _} = :sys.get_state(monitor)
IO.inspect(state, label: "after DATA+END_STREAM")

IO.puts("\n== an illegal frame is caught with client blame ==")
IO.puts("A fresh stream is :idle. DATA before HEADERS has no transition — the peer's fault.")

ViolationCollector.init()
{:ok, server2} = DemoUpstream.start_link()

{:ok, monitor2} =
  Protocol.Monitor.start_link(
    upstream: server2,
    downstream: self(),
    violation_policy: {ViolationCollector, :handle}
  )

Monitor.cast(monitor2, :data)
# Synchronize with the monitor so the violation is recorded before we drain.
:sys.get_state(monitor2)

[violation] = ViolationCollector.drain()
IO.puts(Accord.Violation.Report.format(violation, Protocol.__compiled__()))
