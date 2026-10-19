defmodule Accord.Examples.JobQueueTest do
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.JobQueue.{Protocol, Server, StaleTokenServer}
  alias Accord.Monitor
  alias Accord.Test.{TLACheck, ViolationCollector}

  defp start(opts \\ []) do
    {:ok, queue} = Server.start_link()

    {:ok, monitor} =
      Protocol.Monitor.start_link(
        Keyword.merge(
          [upstream: queue, downstream: self(), violation_policy: :reject],
          opts
        )
      )

    Server.attach_monitor(queue, monitor)
    {queue, monitor}
  end

  describe "conformance" do
    test "checkout, heartbeat, ack with increasing fence tokens" do
      {_queue, monitor} = start(violation_policy: :crash)

      assert {:job, 1} = Monitor.call(monitor, :checkout)
      assert :extended = Monitor.call(monitor, {:heartbeat, 1})
      assert :done = Monitor.call(monitor, {:ack, 1})

      assert {:job, 2} = Monitor.call(monitor, :checkout)
      assert :requeued = Monitor.call(monitor, {:nack, 2})
    end

    test "the visibility timeout arrives as a validated event" do
      {queue, monitor} = start(violation_policy: :crash)

      assert {:job, 1} = Monitor.call(monitor, :checkout)
      assert :expired = Server.expire_lease(queue)

      assert_receive {:lease_expired, 1}
      assert {:idle, data} = :sys.get_state(monitor)
      assert data.tracks.holding == 0
    end
  end

  describe "blame" do
    test "acking after expiry is client blame" do
      {queue, monitor} = start()

      assert {:job, 1} = Monitor.call(monitor, :checkout)
      assert :expired = Server.expire_lease(queue)
      assert_receive {:lease_expired, 1}

      # The worker no longer holds a lease; the ack is not valid in :idle.
      assert {:accord_violation, violation} = Monitor.call(monitor, {:ack, 1})
      assert violation.blame == :client
      assert violation.kind == :invalid_message
    end

    test "acking with the wrong token is client blame on the guard" do
      {_queue, monitor} = start()

      assert {:job, 1} = Monitor.call(monitor, :checkout)
      assert {:accord_violation, violation} = Monitor.call(monitor, {:ack, 99})
      assert violation.blame == :client
      assert violation.kind == :guard_failed
    end

    test "a queue re-issuing fence tokens is server blame on the constraint" do
      {:ok, bad_queue} = StaleTokenServer.start_link()

      {:ok, monitor} =
        Protocol.Monitor.start_link(upstream: bad_queue, violation_policy: :reject)

      assert {:job, 1} = Monitor.call(monitor, :checkout)
      assert :done = Monitor.call(monitor, {:ack, 1})

      # Token 1 again: violates where: token > tracks.fence.
      assert {:accord_violation, violation} = Monitor.call(monitor, :checkout)
      assert violation.blame == :server
      assert violation.kind == :constraint_failed
      assert violation.reply == {:job, 1}
    end

    test "an expiry push for a token the worker does not hold is server blame" do
      {_queue, monitor} = start(violation_policy: {ViolationCollector, :handle})
      ViolationCollector.init()

      assert {:job, 1} = Monitor.call(monitor, :checkout)

      Accord.event(monitor, {:lease_expired, 99})
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.blame == :server
      assert violation.kind == :guard_failed
    end
  end

  describe "model checking" do
    @describetag :tmp_dir

    test "the correct protocol verifies", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Protocol, tmp_dir: tmp_dir)
    end

    test "the leaky lease is caught in three actions", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(
        Accord.Examples.JobQueue.ProtocolLeakyLease,
        :invariant,
        tmp_dir: tmp_dir
      )
    end
  end
end
