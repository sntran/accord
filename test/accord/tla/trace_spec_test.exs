defmodule Accord.TLA.TraceSpecTest do
  @moduledoc """
  Trace validation: real monitor sessions replayed against the spec by
  real TLC, and hand-built divergent traces rejected at the exact step.
  """
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.JobQueue.{Protocol, Server}
  alias Accord.Monitor
  alias Accord.Test.TraceCheck
  alias Accord.TLA.TraceSpec
  alias Accord.Trace

  defp run_session do
    {:ok, collector, sink} = Trace.collector()
    {:ok, queue} = Server.start_link()

    {:ok, monitor} =
      Protocol.Monitor.start_link(
        upstream: queue,
        downstream: self(),
        violation_policy: :crash,
        trace_sink: sink
      )

    Server.attach_monitor(queue, monitor)

    assert {:job, 1} = Monitor.call(monitor, :checkout)
    assert :extended = Monitor.call(monitor, {:heartbeat, 1})
    assert :done = Monitor.call(monitor, {:ack, 1})
    assert {:job, 2} = Monitor.call(monitor, :checkout)
    Server.expire_lease(queue)
    assert_receive {:lease_expired, 2}
    assert {:job, 3} = Monitor.call(monitor, :checkout)
    assert :requeued = Monitor.call(monitor, {:nack, 3})
    assert :stopped = Monitor.call(monitor, :stop)

    # Synchronous barrier so all trace events are emitted.
    _ = :sys.get_state(monitor)
    Trace.collected(collector)
  end

  describe "generation" do
    test "the trace module pins recorded states and synthesizes domains" do
      events = run_session()
      {:ok, spec} = TraceSpec.generate(Protocol, events)

      assert spec.module_name == "AccordExamplesJobQueueProtocolTrace"
      assert spec.trace_tla =~ "EXTENDS AccordExamplesJobQueueProtocol"
      # Initial record plus one per event.
      assert length(String.split(spec.trace_tla, "|->")) > length(events)
      assert spec.trace_tla =~ ~s([state |-> "idle", fence |-> 0, holding |-> 0])
      assert spec.trace_tla =~ "TSpec == TInit /\\ [][TNext]_<<vars, ti>>"
      # Observed fence tokens become the domain — no truncation.
      assert spec.base_tla =~ "fence \\in {0, 1, 2, 3}"
      assert spec.trace_cfg =~ "SPECIFICATION TSpec"
    end

    test "unsupported terms are rejected honestly" do
      events = [
        %Trace.Event{
          seq: 0,
          prev_state: :idle,
          message: {:checkout, self()},
          reply: :empty,
          next_state: :idle,
          tracks: %{fence: 0, holding: 0}
        }
      ]

      assert {:error, {:unsupported_term, pid}} = TraceSpec.generate(Protocol, events)
      assert is_pid(pid)
    end
  end

  describe "replay against real TLC" do
    @describetag :tmp_dir

    test "a real session's trace is a behavior of the spec", %{tmp_dir: tmp_dir} do
      events = run_session()

      assert :ok = TraceCheck.assert_replays(Protocol, events, tmp_dir: tmp_dir)
    end

    test "a divergent trace is rejected at the exact step", %{tmp_dir: tmp_dir} do
      events = run_session()

      # Corrupt one recorded successor: pretend the second checkout left
      # the worker holding token 99 — no protocol action produces that.
      divergent =
        List.update_at(events, 3, fn event ->
          %{event | tracks: %{event.tracks | holding: 99, fence: 99}}
        end)

      # Step 4 of the trace (record 5 counting the initial state) —
      # divergence deadlocks with ti at the last replayed index.
      assert {:diverged_at, step} =
               TraceCheck.assert_diverges(Protocol, divergent, tmp_dir: tmp_dir)

      assert step == 4
    end

    test "a trace violating a where: constraint is rejected", %{tmp_dir: tmp_dir} do
      events = run_session()

      # Fabricate a checkout that re-issues a stale token: the fencing
      # constraint (token > fence) exists precisely to forbid this, and
      # the replay refuses it — the oracle catches a monitor that had
      # failed to enforce the constraint.
      stale = %Trace.Event{
        seq: length(events),
        prev_state: :idle,
        message: :checkout,
        reply: {:job, 1},
        next_state: :working,
        tracks: %{fence: 1, holding: 1}
      }

      # Splice after the first ack (fence is already 1 there... use end
      # of trace where fence = 3): re-issuing token 1 violates > 3.
      divergent =
        events ++
          [%{stale | tracks: %{fence: 1, holding: 1}}]

      assert {:diverged_at, _step} =
               TraceCheck.assert_diverges(Protocol, divergent, tmp_dir: tmp_dir)
    end
  end
end
