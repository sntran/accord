defmodule Accord.Examples.GenstageDemandTest do
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.Demand.{OverEagerProducer, Producer, Protocol}
  alias Accord.Monitor
  alias Accord.Test.{TLACheck, ViolationCollector}

  defp start(producer_mod, opts \\ []) do
    {:ok, producer} = producer_mod.start_link()

    {:ok, monitor} =
      Protocol.Monitor.start_link(
        Keyword.merge(
          [upstream: producer, downstream: self(), violation_policy: :reject],
          opts
        )
      )

    producer_mod.attach_monitor(producer, monitor)
    {producer, monitor}
  end

  describe "conformance" do
    test "events within demand flow through and consume it" do
      {producer, monitor} = start(Producer, violation_policy: :crash)

      assert :ok = Monitor.call(monitor, {:ask, 3})
      assert {:emitted, 2} = Producer.emit(producer, 2)
      assert_receive {:events, 2}

      {_state, data} = :sys.get_state(monitor)
      assert data.tracks.demand == 1
    end

    test "a demand-respecting producer clamps emissions" do
      {producer, monitor} = start(Producer, violation_policy: :crash)

      assert :ok = Monitor.call(monitor, {:ask, 1})
      # Asked to emit 5, clamps to 1 — no violation.
      assert {:emitted, 1} = Producer.emit(producer, 5)
      assert_receive {:events, 1}
    end
  end

  describe "blame" do
    test "over-delivery is server blame on the event guard" do
      ViolationCollector.init()

      {producer, monitor} =
        start(OverEagerProducer, violation_policy: {ViolationCollector, :handle})

      assert :ok = Monitor.call(monitor, {:ask, 1})
      OverEagerProducer.emit(producer, 3)
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.blame == :server
      assert violation.kind == :guard_failed
      # The over-delivered events are not forwarded.
      refute_receive {:events, 3}
    end

    test "asking past max_demand is client blame" do
      {_producer, monitor} = start(Producer)

      assert :ok = Monitor.call(monitor, {:ask, 3})
      assert {:accord_violation, violation} = Monitor.call(monitor, {:ask, 4})
      assert violation.blame == :client
      assert violation.kind == :guard_failed
    end
  end

  describe "model checking" do
    @describetag :tmp_dir

    test "the guarded contract verifies", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Protocol, tmp_dir: tmp_dir)
    end

    test "dropping the guard drives demand negative", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(
        Accord.Examples.Demand.ProtocolUnbounded,
        :invariant,
        tmp_dir: tmp_dir
      )
    end
  end
end
